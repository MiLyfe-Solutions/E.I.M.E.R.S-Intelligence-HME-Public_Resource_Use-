import V185TrunkScan23Chunk0187

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1112691 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 3]
def baseStart_1112691 : Nat := 118140960795 + 1112691 * 2 ^ 59
def prefixEnd_1112691 : Nat := 4983230072969 + 3 ^ 40 * 1112691 * 2
def baseEnd_1112691 : Nat := 571345302932011325045333

theorem tailTrace_1112691 : CollatzResearch.WordTrace tailWord_1112691 prefixEnd_1112691 571345302932011325045333 := by
  unfold tailWord_1112691
  simp only [CollatzResearch.WordTrace]
  refine ⟨40583174811918014338649927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27055449874612009559099951 40583174811918014338649927)
  ·
    refine ⟨60874762217877021507974891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40583174811918014338649927 60874762217877021507974891)
    ·
      refine ⟨91312143326815532261962337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60874762217877021507974891 91312143326815532261962337)
      ·
        refine ⟨68484107495111649196471753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91312143326815532261962337 68484107495111649196471753)
        ·
          refine ⟨51363080621333736897353815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68484107495111649196471753 51363080621333736897353815)
          ·
            refine ⟨77044620932000605346030723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51363080621333736897353815 77044620932000605346030723)
            ·
              refine ⟨115566931398000908019046085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77044620932000605346030723 115566931398000908019046085)
              ·
                refine ⟨21668799637125170253571141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115566931398000908019046085 21668799637125170253571141)
                ·
                  refine ⟨4062899931960969422544589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21668799637125170253571141 4062899931960969422544589)
                  ·
                    refine ⟨1523587474485363533454221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4062899931960969422544589 1523587474485363533454221)
                    ·
                      refine ⟨571345302932011325045333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1523587474485363533454221 571345302932011325045333)
                      ·
                        rfl

theorem cell23_1112691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_1112691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112691 prefixEnd_1112691 := by exact prefixLift 1112691
  have htrace : WordTrace (prefixWord ++ tailWord_1112691) baseStart_1112691 baseEnd_1112691 := by
    simpa [prefixWord, tailWord_1112691, baseEnd_1112691] using wordTrace_append hprefix tailTrace_1112691
  have hstable : (prefixWord ++ tailWord_1112691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112691).length < 2 ^ (prefixWord ++ tailWord_1112691).sum := by decide
  have hdescent : baseEnd_1112691 < baseStart_1112691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112761 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1112761 : Nat := 118140960795 + 1112761 * 2 ^ 59
def prefixEnd_1112761 : Nat := 4983230072969 + 3 ^ 40 * 1112761 * 2
def baseEnd_1112761 : Nat := 571381246577826051170011

theorem tailTrace_1112761 : CollatzResearch.WordTrace tailWord_1112761 prefixEnd_1112761 571381246577826051170011 := by
  unfold tailWord_1112761
  simp only [CollatzResearch.WordTrace]
  refine ⟨40585727921664416293698137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27057151947776277529132091 40585727921664416293698137)
  ·
    refine ⟨30439295941248312220273603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40585727921664416293698137 30439295941248312220273603)
    ·
      refine ⟨45658943911872468330410405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30439295941248312220273603 45658943911872468330410405)
      ·
        refine ⟨8561051983476087811951951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45658943911872468330410405 8561051983476087811951951)
        ·
          refine ⟨12841577975214131717927927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8561051983476087811951951 12841577975214131717927927)
          ·
            refine ⟨19262366962821197576891891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12841577975214131717927927 19262366962821197576891891)
            ·
              refine ⟨28893550444231796365337837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19262366962821197576891891 28893550444231796365337837)
              ·
                refine ⟨10835081416586923637001689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28893550444231796365337837 10835081416586923637001689)
                ·
                  refine ⟨8126311062440192727751267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10835081416586923637001689 8126311062440192727751267)
                  ·
                    refine ⟨12189466593660289091626901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8126311062440192727751267 12189466593660289091626901)
                    ·
                      refine ⟨571381246577826051170011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12189466593660289091626901 571381246577826051170011)
                      ·
                        rfl

theorem cell23_1112761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1112761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112761 prefixEnd_1112761 := by exact prefixLift 1112761
  have htrace : WordTrace (prefixWord ++ tailWord_1112761) baseStart_1112761 baseEnd_1112761 := by
    simpa [prefixWord, tailWord_1112761, baseEnd_1112761] using wordTrace_append hprefix tailTrace_1112761
  have hstable : (prefixWord ++ tailWord_1112761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112761).length < 2 ^ (prefixWord ++ tailWord_1112761).sum := by decide
  have hdescent : baseEnd_1112761 < baseStart_1112761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112811 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 5]
def baseStart_1112811 : Nat := 118140960795 + 1112811 * 2 ^ 59
def prefixEnd_1112811 : Nat := 4983230072969 + 3 ^ 40 * 1112811 * 2
def baseEnd_1112811 : Nat := 571406920610550855544781

theorem tailTrace_1112811 : CollatzResearch.WordTrace tailWord_1112811 prefixEnd_1112811 571406920610550855544781 := by
  unfold tailWord_1112811
  simp only [CollatzResearch.WordTrace]
  refine ⟨40587551571483274833018287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27058367714322183222012191 40587551571483274833018287)
  ·
    refine ⟨60881327357224912249527431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40587551571483274833018287 60881327357224912249527431)
    ·
      refine ⟨91321991035837368374291147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60881327357224912249527431 91321991035837368374291147)
      ·
        refine ⟨136982986553756052561436721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91321991035837368374291147 136982986553756052561436721)
        ·
          refine ⟨102737239915317039421077541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136982986553756052561436721 102737239915317039421077541)
          ·
            refine ⟨19263232484121944891452039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102737239915317039421077541 19263232484121944891452039)
            ·
              refine ⟨28894848726182917337178059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19263232484121944891452039 28894848726182917337178059)
              ·
                refine ⟨43342273089274376005767089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28894848726182917337178059 43342273089274376005767089)
                ·
                  refine ⟨32506704816955782004325317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43342273089274376005767089 32506704816955782004325317)
                  ·
                    refine ⟨6095007153179209125810997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32506704816955782004325317 6095007153179209125810997)
                    ·
                      refine ⟨571406920610550855544781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6095007153179209125810997 571406920610550855544781)
                      ·
                        rfl

theorem cell23_1112811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_1112811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112811 prefixEnd_1112811 := by exact prefixLift 1112811
  have htrace : WordTrace (prefixWord ++ tailWord_1112811) baseStart_1112811 baseEnd_1112811 := by
    simpa [prefixWord, tailWord_1112811, baseEnd_1112811] using wordTrace_append hprefix tailTrace_1112811
  have hstable : (prefixWord ++ tailWord_1112811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112811).length < 2 ^ (prefixWord ++ tailWord_1112811).sum := by decide
  have hdescent : baseEnd_1112811 < baseStart_1112811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112825 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 2, 3, 2]
def baseStart_1112825 : Nat := 118140960795 + 1112825 * 2 ^ 59
def prefixEnd_1112825 : Nat := 4983230072969 + 3 ^ 40 * 1112825 * 2
def baseEnd_1112825 : Nat := 571414109339713800769717

theorem tailTrace_1112825 : CollatzResearch.WordTrace tailWord_1112825 prefixEnd_1112825 571414109339713800769717 := by
  unfold tailWord_1112825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40588062193432555224027929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27058708128955036816018619 40588062193432555224027929)
  ·
    refine ⟨30441046645074416418020947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40588062193432555224027929 30441046645074416418020947)
    ·
      refine ⟨45661569967611624627031421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30441046645074416418020947 45661569967611624627031421)
      ·
        refine ⟨17123088737854359235136783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45661569967611624627031421 17123088737854359235136783)
        ·
          refine ⟨25684633106781538852705175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17123088737854359235136783 25684633106781538852705175)
          ·
            refine ⟨38526949660172308279057763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25684633106781538852705175 38526949660172308279057763)
            ·
              refine ⟨57790424490258462418586645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38526949660172308279057763 57790424490258462418586645)
              ·
                refine ⟨2708926147980865425871249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57790424490258462418586645 2708926147980865425871249)
                ·
                  refine ⟨2031694610985649069403437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2708926147980865425871249 2031694610985649069403437)
                  ·
                    refine ⟨761885479119618401026289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031694610985649069403437 761885479119618401026289)
                    ·
                      refine ⟨571414109339713800769717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761885479119618401026289 571414109339713800769717)
                      ·
                        rfl

theorem cell23_1112825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_1112825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112825 prefixEnd_1112825 := by exact prefixLift 1112825
  have htrace : WordTrace (prefixWord ++ tailWord_1112825) baseStart_1112825 baseEnd_1112825 := by
    simpa [prefixWord, tailWord_1112825, baseEnd_1112825] using wordTrace_append hprefix tailTrace_1112825
  have hstable : (prefixWord ++ tailWord_1112825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112825).length < 2 ^ (prefixWord ++ tailWord_1112825).sum := by decide
  have hdescent : baseEnd_1112825 < baseStart_1112825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112858 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1112858 : Nat := 118140960795 + 1112858 * 2 ^ 59
def prefixEnd_1112858 : Nat := 4983230072969 + 3 ^ 40 * 1112858 * 2
def baseEnd_1112858 : Nat := 571431054201312171657065

theorem tailTrace_1112858 : CollatzResearch.WordTrace tailWord_1112858 prefixEnd_1112858 571431054201312171657065 := by
  unfold tailWord_1112858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147316450578250464994807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27059510534875334573319485 10147316450578250464994807)
  ·
    refine ⟨15220974675867375697492211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10147316450578250464994807 15220974675867375697492211)
    ·
      refine ⟨22831462013801063546238317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15220974675867375697492211 22831462013801063546238317)
      ·
        refine ⟨8561798255175398829839369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22831462013801063546238317 8561798255175398829839369)
        ·
          refine ⟨6421348691381549122379527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8561798255175398829839369 6421348691381549122379527)
          ·
            refine ⟨9632023037072323683569291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6421348691381549122379527 9632023037072323683569291)
            ·
              refine ⟨14448034555608485525353937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9632023037072323683569291 14448034555608485525353937)
              ·
                refine ⟨10836025916706364144015453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14448034555608485525353937 10836025916706364144015453)
                ·
                  refine ⟨4063509718764886554005795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10836025916706364144015453 4063509718764886554005795)
                  ·
                    refine ⟨6095264578147329831008693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4063509718764886554005795 6095264578147329831008693)
                    ·
                      refine ⟨571431054201312171657065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6095264578147329831008693 571431054201312171657065)
                      ·
                        rfl

theorem cell23_1112858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1112858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112858 prefixEnd_1112858 := by exact prefixLift 1112858
  have htrace : WordTrace (prefixWord ++ tailWord_1112858) baseStart_1112858 baseEnd_1112858 := by
    simpa [prefixWord, tailWord_1112858, baseEnd_1112858] using wordTrace_append hprefix tailTrace_1112858
  have hstable : (prefixWord ++ tailWord_1112858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112858).length < 2 ^ (prefixWord ++ tailWord_1112858).sum := by decide
  have hdescent : baseEnd_1112858 < baseStart_1112858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112866 : List Nat := [3, 3, 1, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_1112866 : Nat := 118140960795 + 1112866 * 2 ^ 59
def prefixEnd_1112866 : Nat := 4983230072969 + 3 ^ 40 * 1112866 * 2
def baseEnd_1112866 : Nat := 571435162046548140357029

theorem tailTrace_1112866 : CollatzResearch.WordTrace tailWord_1112866 prefixEnd_1112866 571435162046548140357029 := by
  unfold tailWord_1112866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147389396571004806567613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27059705057522679484180301 10147389396571004806567613)
  ·
    refine ⟨3805271023714126802462855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10147389396571004806567613 3805271023714126802462855)
    ·
      refine ⟨5707906535571190203694283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3805271023714126802462855 5707906535571190203694283)
      ·
        refine ⟨8561859803356785305541425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5707906535571190203694283 8561859803356785305541425)
        ·
          refine ⟨6421394852517588979156069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8561859803356785305541425 6421394852517588979156069)
          ·
            refine ⟨1204011534847047933591763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6421394852517588979156069 1204011534847047933591763)
            ·
              refine ⟨1806017302270571900387645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204011534847047933591763 1806017302270571900387645)
              ·
                refine ⟨677256488351464462645367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1806017302270571900387645 677256488351464462645367)
                ·
                  refine ⟨1015884732527196693968051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677256488351464462645367 1015884732527196693968051)
                  ·
                    refine ⟨1523827098790795040952077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1015884732527196693968051 1523827098790795040952077)
                    ·
                      refine ⟨571435162046548140357029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1523827098790795040952077 571435162046548140357029)
                      ·
                        rfl

theorem cell23_1112866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_1112866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112866 prefixEnd_1112866 := by exact prefixLift 1112866
  have htrace : WordTrace (prefixWord ++ tailWord_1112866) baseStart_1112866 baseEnd_1112866 := by
    simpa [prefixWord, tailWord_1112866, baseEnd_1112866] using wordTrace_append hprefix tailTrace_1112866
  have hstable : (prefixWord ++ tailWord_1112866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112866).length < 2 ^ (prefixWord ++ tailWord_1112866).sum := by decide
  have hdescent : baseEnd_1112866 < baseStart_1112866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112909 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1112909 : Nat := 118140960795 + 1112909 * 2 ^ 59
def prefixEnd_1112909 : Nat := 4983230072969 + 3 ^ 40 * 1112909 * 2
def baseEnd_1112909 : Nat := 571457241714691472119331

theorem tailTrace_1112909 : CollatzResearch.WordTrace tailWord_1112909 prefixEnd_1112909 571457241714691472119331 := by
  unfold tailWord_1112909
  simp only [CollatzResearch.WordTrace]
  refine ⟨40591125925128237570085781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27060750616752158380057187 40591125925128237570085781)
  ·
    refine ⟨1902709027740386136097771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40591125925128237570085781 1902709027740386136097771)
    ·
      refine ⟨2854063541610579204146657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902709027740386136097771 2854063541610579204146657)
      ·
        refine ⟨2140547656207934403109993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2854063541610579204146657 2140547656207934403109993)
        ·
          refine ⟨1605410742155950802332495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2140547656207934403109993 1605410742155950802332495)
          ·
            refine ⟨2408116113233926203498743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605410742155950802332495 2408116113233926203498743)
            ·
              refine ⟨3612174169850889305248115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408116113233926203498743 3612174169850889305248115)
              ·
                refine ⟨5418261254776333957872173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612174169850889305248115 5418261254776333957872173)
                ·
                  refine ⟨2031847970541125234202065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5418261254776333957872173 2031847970541125234202065)
                  ·
                    refine ⟨1523885977905843925651549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2031847970541125234202065 1523885977905843925651549)
                    ·
                      refine ⟨571457241714691472119331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1523885977905843925651549 571457241714691472119331)
                      ·
                        rfl

theorem cell23_1112909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1112909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112909 prefixEnd_1112909 := by exact prefixLift 1112909
  have htrace : WordTrace (prefixWord ++ tailWord_1112909) baseStart_1112909 baseEnd_1112909 := by
    simpa [prefixWord, tailWord_1112909, baseEnd_1112909] using wordTrace_append hprefix tailTrace_1112909
  have hstable : (prefixWord ++ tailWord_1112909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112909).length < 2 ^ (prefixWord ++ tailWord_1112909).sum := by decide
  have hdescent : baseEnd_1112909 < baseStart_1112909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112995 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 3]
def baseStart_1112995 : Nat := 118140960795 + 1112995 * 2 ^ 59
def prefixEnd_1112995 : Nat := 4983230072969 + 3 ^ 40 * 1112995 * 2
def baseEnd_1112995 : Nat := 571501401050978135643935

theorem tailTrace_1112995 : CollatzResearch.WordTrace tailWord_1112995 prefixEnd_1112995 571501401050978135643935 := by
  unfold tailWord_1112995
  simp only [CollatzResearch.WordTrace]
  refine ⟨40594262602816674257716439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27062841735211116171810959 40594262602816674257716439)
  ·
    refine ⟨60891393904225011386574659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40594262602816674257716439 60891393904225011386574659)
    ·
      refine ⟨91337090856337517079861989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60891393904225011386574659 91337090856337517079861989)
      ·
        refine ⟨17125704535563284452474123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91337090856337517079861989 17125704535563284452474123)
        ·
          refine ⟨25688556803344926678711185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17125704535563284452474123 25688556803344926678711185)
          ·
            refine ⟨19266417602508695009033389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25688556803344926678711185 19266417602508695009033389)
            ·
              refine ⟨7224906600940760628387521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19266417602508695009033389 7224906600940760628387521)
              ·
                refine ⟨5418679950705570471290641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7224906600940760628387521 5418679950705570471290641)
                ·
                  refine ⟨4064009963029177853467981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418679950705570471290641 4064009963029177853467981)
                  ·
                    refine ⟨1524003736135941695050493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4064009963029177853467981 1524003736135941695050493)
                    ·
                      refine ⟨571501401050978135643935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1524003736135941695050493 571501401050978135643935)
                      ·
                        rfl

theorem cell23_1112995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_1112995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112995 prefixEnd_1112995 := by exact prefixLift 1112995
  have htrace : WordTrace (prefixWord ++ tailWord_1112995) baseStart_1112995 baseEnd_1112995 := by
    simpa [prefixWord, tailWord_1112995, baseEnd_1112995] using wordTrace_append hprefix tailTrace_1112995
  have hstable : (prefixWord ++ tailWord_1112995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112995).length < 2 ^ (prefixWord ++ tailWord_1112995).sum := by decide
  have hdescent : baseEnd_1112995 < baseStart_1112995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113035 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 4]
def baseStart_1113035 : Nat := 118140960795 + 1113035 * 2 ^ 59
def prefixEnd_1113035 : Nat := 4983230072969 + 3 ^ 40 * 1113035 * 2
def baseEnd_1113035 : Nat := 571521940277157979143751

theorem tailTrace_1113035 : CollatzResearch.WordTrace tailWord_1113035 prefixEnd_1113035 571521940277157979143751 := by
  unfold tailWord_1113035
  simp only [CollatzResearch.WordTrace]
  refine ⟨40595721522671761089172559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27063814348447840726115039 40595721522671761089172559)
  ·
    refine ⟨60893582284007641633758839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40595721522671761089172559 60893582284007641633758839)
    ·
      refine ⟨91340373426011462450638259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60893582284007641633758839 91340373426011462450638259)
      ·
        refine ⟨137010560139017193675957389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91340373426011462450638259 137010560139017193675957389)
        ·
          refine ⟨51378960052131447628484021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137010560139017193675957389 51378960052131447628484021)
          ·
            refine ⟨4816777504887323215170377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51378960052131447628484021 4816777504887323215170377)
            ·
              refine ⟨3612583128665492411377783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4816777504887323215170377 3612583128665492411377783)
              ·
                refine ⟨5418874692998238617066675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612583128665492411377783 5418874692998238617066675)
                ·
                  refine ⟨8128312039497357925600013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418874692998238617066675 8128312039497357925600013)
                  ·
                    refine ⟨3048117014811509222100005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8128312039497357925600013 3048117014811509222100005)
                    ·
                      refine ⟨571521940277157979143751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3048117014811509222100005 571521940277157979143751)
                      ·
                        rfl

theorem cell23_1113035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 4].length) (baseStart_1113035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113035 prefixEnd_1113035 := by exact prefixLift 1113035
  have htrace : WordTrace (prefixWord ++ tailWord_1113035) baseStart_1113035 baseEnd_1113035 := by
    simpa [prefixWord, tailWord_1113035, baseEnd_1113035] using wordTrace_append hprefix tailTrace_1113035
  have hstable : (prefixWord ++ tailWord_1113035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113035).length < 2 ^ (prefixWord ++ tailWord_1113035).sum := by decide
  have hdescent : baseEnd_1113035 < baseStart_1113035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113086 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1113086 : Nat := 118140960795 + 1113086 * 2 ^ 59
def prefixEnd_1113086 : Nat := 4983230072969 + 3 ^ 40 * 1113086 * 2
def baseEnd_1113086 : Nat := 571548127790537279606017

theorem tailTrace_1113086 : CollatzResearch.WordTrace tailWord_1113086 prefixEnd_1113086 571548127790537279606017 := by
  unfold tailWord_1113086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5074697705685874599909889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27065054430324664532852741 5074697705685874599909889)
  ·
    refine ⟨3806023279264405949932417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5074697705685874599909889 3806023279264405949932417)
    ·
      refine ⟨2854517459448304462449313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3806023279264405949932417 2854517459448304462449313)
      ·
        refine ⟨2140888094586228346836985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2854517459448304462449313 2140888094586228346836985)
        ·
          refine ⟨1605666070939671260127739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2140888094586228346836985 1605666070939671260127739)
          ·
            refine ⟨2408499106409506890191609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605666070939671260127739 2408499106409506890191609)
            ·
              refine ⟨1806374329807130167643707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408499106409506890191609 1806374329807130167643707)
              ·
                refine ⟨2709561494710695251465561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806374329807130167643707 2709561494710695251465561)
                ·
                  refine ⟨2032171121033021438599171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2709561494710695251465561 2032171121033021438599171)
                  ·
                    refine ⟨3048256681549532157898757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2032171121033021438599171 3048256681549532157898757)
                    ·
                      refine ⟨571548127790537279606017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3048256681549532157898757 571548127790537279606017)
                      ·
                        rfl

theorem cell23_1113086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1113086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113086 prefixEnd_1113086 := by exact prefixLift 1113086
  have htrace : WordTrace (prefixWord ++ tailWord_1113086) baseStart_1113086 baseEnd_1113086 := by
    simpa [prefixWord, tailWord_1113086, baseEnd_1113086] using wordTrace_append hprefix tailTrace_1113086
  have hstable : (prefixWord ++ tailWord_1113086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113086).length < 2 ^ (prefixWord ++ tailWord_1113086).sum := by decide
  have hdescent : baseEnd_1113086 < baseStart_1113086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113089 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1113089 : Nat := 118140960795 + 1113089 * 2 ^ 59
def prefixEnd_1113089 : Nat := 4983230072969 + 3 ^ 40 * 1113089 * 2
def baseEnd_1113089 : Nat := 571549668232500767868503

theorem tailTrace_1113089 : CollatzResearch.WordTrace tailWord_1113089 prefixEnd_1113089 571549668232500767868503 := by
  unfold tailWord_1113089
  simp only [CollatzResearch.WordTrace]
  refine ⟨40597691064476128311638321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27065127376317418874425547 40597691064476128311638321)
  ·
    refine ⟨30448268298357096233728741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40597691064476128311638321 30448268298357096233728741)
    ·
      refine ⟨5709050305941955543824139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30448268298357096233728741 5709050305941955543824139)
      ·
        refine ⟨8563575458912933315736209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5709050305941955543824139 8563575458912933315736209)
        ·
          refine ⟨6422681594184699986802157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8563575458912933315736209 6422681594184699986802157)
          ·
            refine ⟨2408505597819262495050809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6422681594184699986802157 2408505597819262495050809)
            ·
              refine ⟨1806379198364446871288107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408505597819262495050809 1806379198364446871288107)
              ·
                refine ⟨2709568797546670306932161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806379198364446871288107 2709568797546670306932161)
                ·
                  refine ⟨2032176598160002730199121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2709568797546670306932161 2032176598160002730199121)
                  ·
                    refine ⟨1524132448620002047649341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2032176598160002730199121 1524132448620002047649341)
                    ·
                      refine ⟨571549668232500767868503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1524132448620002047649341 571549668232500767868503)
                      ·
                        rfl

theorem cell23_1113089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1113089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113089 prefixEnd_1113089 := by exact prefixLift 1113089
  have htrace : WordTrace (prefixWord ++ tailWord_1113089) baseStart_1113089 baseEnd_1113089 := by
    simpa [prefixWord, tailWord_1113089, baseEnd_1113089] using wordTrace_append hprefix tailTrace_1113089
  have hstable : (prefixWord ++ tailWord_1113089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113089).length < 2 ^ (prefixWord ++ tailWord_1113089).sum := by decide
  have hdescent : baseEnd_1113089 < baseStart_1113089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113122 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1113122 : Nat := 118140960795 + 1113122 * 2 ^ 59
def prefixEnd_1113122 : Nat := 4983230072969 + 3 ^ 40 * 1113122 * 2
def baseEnd_1113122 : Nat := 190522204364699712918617

theorem tailTrace_1113122 : CollatzResearch.WordTrace tailWord_1113122 prefixEnd_1113122 190522204364699712918617 := by
  unfold tailWord_1113122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10149723668339143736897405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27065929782237716631726413 10149723668339143736897405)
  ·
    refine ⟨3806146375627178901336527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10149723668339143736897405 3806146375627178901336527)
    ·
      refine ⟨5709219563440768352004791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3806146375627178901336527 5709219563440768352004791)
      ·
        refine ⟨8563829345161152528007187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5709219563440768352004791 8563829345161152528007187)
        ·
          refine ⟨12845744017741728792010781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8563829345161152528007187 12845744017741728792010781)
          ·
            refine ⟨4817154006653148297004043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12845744017741728792010781 4817154006653148297004043)
            ·
              refine ⟨7225731009979722445506065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4817154006653148297004043 7225731009979722445506065)
              ·
                refine ⟨5419298257484791834129549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7225731009979722445506065 5419298257484791834129549)
                ·
                  refine ⟨2032236846556796937798581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5419298257484791834129549 2032236846556796937798581)
                  ·
                    refine ⟨190522204364699712918617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2032236846556796937798581 190522204364699712918617)
                    ·
                      rfl

theorem cell23_1113122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1113122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113122 prefixEnd_1113122 := by exact prefixLift 1113122
  have htrace : WordTrace (prefixWord ++ tailWord_1113122) baseStart_1113122 baseEnd_1113122 := by
    simpa [prefixWord, tailWord_1113122, baseEnd_1113122] using wordTrace_append hprefix tailTrace_1113122
  have hstable : (prefixWord ++ tailWord_1113122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113122).length < 2 ^ (prefixWord ++ tailWord_1113122).sum := by decide
  have hdescent : baseEnd_1113122 < baseStart_1113122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113152 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 4, 4]
def baseStart_1113152 : Nat := 118140960795 + 1113152 * 2 ^ 59
def prefixEnd_1113152 : Nat := 4983230072969 + 3 ^ 40 * 1113152 * 2
def baseEnd_1113152 : Nat := 190527339171244673793571

theorem tailTrace_1113152 : CollatzResearch.WordTrace tailWord_1113152 prefixEnd_1113152 190527339171244673793571 := by
  unfold tailWord_1113152
  simp only [CollatzResearch.WordTrace]
  refine ⟨20299994431623945035590855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27066659242165260047454473 20299994431623945035590855)
  ·
    refine ⟨30449991647435917553386283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20299994431623945035590855 30449991647435917553386283)
    ·
      refine ⟨45674987471153876330079425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30449991647435917553386283 45674987471153876330079425)
      ·
        refine ⟨34256240603365407247559569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45674987471153876330079425 34256240603365407247559569)
        ·
          refine ⟨25692180452524055435669677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34256240603365407247559569 25692180452524055435669677)
          ·
            refine ⟨9634567669696520788376129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25692180452524055435669677 9634567669696520788376129)
            ·
              refine ⟨7225925752272390591282097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9634567669696520788376129 7225925752272390591282097)
              ·
                refine ⟨5419444314204292943461573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7225925752272390591282097 5419444314204292943461573)
                ·
                  refine ⟨1016145808913304926899045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5419444314204292943461573 1016145808913304926899045)
                  ·
                    refine ⟨190527339171244673793571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1016145808913304926899045 190527339171244673793571)
                    ·
                      rfl

theorem cell23_1113152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 4].length) (baseStart_1113152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113152 prefixEnd_1113152 := by exact prefixLift 1113152
  have htrace : WordTrace (prefixWord ++ tailWord_1113152) baseStart_1113152 baseEnd_1113152 := by
    simpa [prefixWord, tailWord_1113152, baseEnd_1113152] using wordTrace_append hprefix tailTrace_1113152
  have hstable : (prefixWord ++ tailWord_1113152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113152).length < 2 ^ (prefixWord ++ tailWord_1113152).sum := by decide
  have hdescent : baseEnd_1113152 < baseStart_1113152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113159 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_1113159 : Nat := 118140960795 + 1113159 * 2 ^ 59
def prefixEnd_1113159 : Nat := 4983230072969 + 3 ^ 40 * 1113159 * 2
def baseEnd_1113159 : Nat := 571585611878315493993181

theorem tailTrace_1113159 : CollatzResearch.WordTrace tailWord_1113159 prefixEnd_1113159 571585611878315493993181 := by
  unfold tailWord_1113159
  simp only [CollatzResearch.WordTrace]
  refine ⟨40600244174222530266686531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27066829449481686844457687 40600244174222530266686531)
  ·
    refine ⟨60900366261333795400029797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40600244174222530266686531 60900366261333795400029797)
    ·
      refine ⟨11418818674000086637505587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60900366261333795400029797 11418818674000086637505587)
      ·
        refine ⟨17128228011000129956258381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11418818674000086637505587 17128228011000129956258381)
        ·
          refine ⟨6423085504125048733596893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17128228011000129956258381 6423085504125048733596893)
          ·
            refine ⟨2408657064046893275098835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6423085504125048733596893 2408657064046893275098835)
            ·
              refine ⟨3612985596070339912648253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408657064046893275098835 3612985596070339912648253)
              ·
                refine ⟨1354869598526377467243095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3612985596070339912648253 1354869598526377467243095)
                ·
                  refine ⟨2032304397789566200864643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354869598526377467243095 2032304397789566200864643)
                  ·
                    refine ⟨3048456596684349301296965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2032304397789566200864643 3048456596684349301296965)
                    ·
                      refine ⟨571585611878315493993181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3048456596684349301296965 571585611878315493993181)
                      ·
                        rfl

theorem cell23_1113159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_1113159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113159 prefixEnd_1113159 := by exact prefixLift 1113159
  have htrace : WordTrace (prefixWord ++ tailWord_1113159) baseStart_1113159 baseEnd_1113159 := by
    simpa [prefixWord, tailWord_1113159, baseEnd_1113159] using wordTrace_append hprefix tailTrace_1113159
  have hstable : (prefixWord ++ tailWord_1113159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113159).length < 2 ^ (prefixWord ++ tailWord_1113159).sum := by decide
  have hdescent : baseEnd_1113159 < baseStart_1113159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113169 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 2, 4]
def baseStart_1113169 : Nat := 118140960795 + 1113169 * 2 ^ 59
def prefixEnd_1113169 : Nat := 4983230072969 + 3 ^ 40 * 1113169 * 2
def baseEnd_1113169 : Nat := 190530248894953484956045

theorem tailTrace_1113169 : CollatzResearch.WordTrace tailWord_1113169 prefixEnd_1113169 190530248894953484956045 := by
  unfold tailWord_1113169
  simp only [CollatzResearch.WordTrace]
  refine ⟨40600608904186301974550561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27067072602790867983033707 40600608904186301974550561)
  ·
    refine ⟨30450456678139726480912921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40600608904186301974550561 30450456678139726480912921)
    ·
      refine ⟨22837842508604794860684691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30450456678139726480912921 22837842508604794860684691)
      ·
        refine ⟨34256763762907192291027037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22837842508604794860684691 34256763762907192291027037)
        ·
          refine ⟨12846286411090197109135139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34256763762907192291027037 12846286411090197109135139)
          ·
            refine ⟨19269429616635295663702709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12846286411090197109135139 19269429616635295663702709)
            ·
              refine ⟨1806509026559558968472129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19269429616635295663702709 1806509026559558968472129)
              ·
                refine ⟨1354881769919669226354097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1806509026559558968472129 1354881769919669226354097)
                ·
                  refine ⟨1016161327439751919765573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1354881769919669226354097 1016161327439751919765573)
                  ·
                    refine ⟨190530248894953484956045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1016161327439751919765573 190530248894953484956045)
                    ·
                      rfl

theorem cell23_1113169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_1113169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113169 prefixEnd_1113169 := by exact prefixLift 1113169
  have htrace : WordTrace (prefixWord ++ tailWord_1113169) baseStart_1113169 baseEnd_1113169 := by
    simpa [prefixWord, tailWord_1113169, baseEnd_1113169] using wordTrace_append hprefix tailTrace_1113169
  have hstable : (prefixWord ++ tailWord_1113169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113169).length < 2 ^ (prefixWord ++ tailWord_1113169).sum := by decide
  have hdescent : baseEnd_1113169 < baseStart_1113169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113172 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1113172 : Nat := 118140960795 + 1113172 * 2 ^ 59
def prefixEnd_1113172 : Nat := 4983230072969 + 3 ^ 40 * 1113172 * 2
def baseEnd_1113172 : Nat := 571592287126823943130621

theorem tailTrace_1113172 : CollatzResearch.WordTrace tailWord_1113172 prefixEnd_1113172 571592287126823943130621 := by
  unfold tailWord_1113172
  simp only [CollatzResearch.WordTrace]
  refine ⟨20300359161587716743454885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27067145548783622324606513 20300359161587716743454885)
  ·
    refine ⟨3806317342797696889397791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20300359161587716743454885 3806317342797696889397791)
    ·
      refine ⟨5709476014196545334096687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3806317342797696889397791 5709476014196545334096687)
      ·
        refine ⟨8564214021294818001145031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5709476014196545334096687 8564214021294818001145031)
        ·
          refine ⟨12846321031942227001717547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8564214021294818001145031 12846321031942227001717547)
          ·
            refine ⟨19269481547913340502576321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12846321031942227001717547 19269481547913340502576321)
            ·
              refine ⟨14452111160935005376932241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19269481547913340502576321 14452111160935005376932241)
              ·
                refine ⟨10839083370701254032699181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14452111160935005376932241 10839083370701254032699181)
                ·
                  refine ⟨4064656264012970262262193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10839083370701254032699181 4064656264012970262262193)
                  ·
                    refine ⟨3048492198009727696696645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4064656264012970262262193 3048492198009727696696645)
                    ·
                      refine ⟨571592287126823943130621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3048492198009727696696645 571592287126823943130621)
                      ·
                        rfl

theorem cell23_1113172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1113172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113172 prefixEnd_1113172 := by exact prefixLift 1113172
  have htrace : WordTrace (prefixWord ++ tailWord_1113172) baseStart_1113172 baseEnd_1113172 := by
    simpa [prefixWord, tailWord_1113172, baseEnd_1113172] using wordTrace_append hprefix tailTrace_1113172
  have hstable : (prefixWord ++ tailWord_1113172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113172).length < 2 ^ (prefixWord ++ tailWord_1113172).sum := by decide
  have hdescent : baseEnd_1113172 < baseStart_1113172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113175 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1113175 : Nat := 118140960795 + 1113175 * 2 ^ 59
def prefixEnd_1113175 : Nat := 4983230072969 + 3 ^ 40 * 1113175 * 2
def baseEnd_1113175 : Nat := 571593827568787431393107

theorem tailTrace_1113175 : CollatzResearch.WordTrace tailWord_1113175 prefixEnd_1113175 571593827568787431393107 := by
  unfold tailWord_1113175
  simp only [CollatzResearch.WordTrace]
  refine ⟨40600827742164564999268979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27067218494776376666179319 40600827742164564999268979)
  ·
    refine ⟨60901241613246847498903469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40600827742164564999268979 60901241613246847498903469)
    ·
      refine ⟨22837965604967567812088801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60901241613246847498903469 22837965604967567812088801)
      ·
        refine ⟨17128474203725675859066601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22837965604967567812088801 17128474203725675859066601)
        ·
          refine ⟨12846355652794256894299951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17128474203725675859066601 12846355652794256894299951)
          ·
            refine ⟨19269533479191385341449927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12846355652794256894299951 19269533479191385341449927)
            ·
              refine ⟨28904300218787078012174891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19269533479191385341449927 28904300218787078012174891)
              ·
                refine ⟨43356450328180617018262337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28904300218787078012174891 43356450328180617018262337)
                ·
                  refine ⟨32517337746135462763696753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43356450328180617018262337 32517337746135462763696753)
                  ·
                    refine ⟨24388003309601597072772565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32517337746135462763696753 24388003309601597072772565)
                    ·
                      refine ⟨571593827568787431393107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24388003309601597072772565 571593827568787431393107)
                      ·
                        rfl

theorem cell23_1113175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1113175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113175 prefixEnd_1113175 := by exact prefixLift 1113175
  have htrace : WordTrace (prefixWord ++ tailWord_1113175) baseStart_1113175 baseEnd_1113175 := by
    simpa [prefixWord, tailWord_1113175, baseEnd_1113175] using wordTrace_append hprefix tailTrace_1113175
  have hstable : (prefixWord ++ tailWord_1113175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113175).length < 2 ^ (prefixWord ++ tailWord_1113175).sum := by decide
  have hdescent : baseEnd_1113175 < baseStart_1113175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113176 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 3, 2, 2]
def baseStart_1113176 : Nat := 118140960795 + 1113176 * 2 ^ 59
def prefixEnd_1113176 : Nat := 4983230072969 + 3 ^ 40 * 1113176 * 2
def baseEnd_1113176 : Nat := 571594341049441927480603

theorem tailTrace_1113176 : CollatzResearch.WordTrace tailWord_1113176 prefixEnd_1113176 571594341049441927480603 := by
  unfold tailWord_1113176
  simp only [CollatzResearch.WordTrace]
  refine ⟨20300432107580471085027691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27067242810107294780036921 20300432107580471085027691)
  ·
    refine ⟨30450648161370706627541537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20300432107580471085027691 30450648161370706627541537)
    ·
      refine ⟨22837986121028029970656153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30450648161370706627541537 22837986121028029970656153)
      ·
        refine ⟨17128489590771022477992115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22837986121028029970656153 17128489590771022477992115)
        ·
          refine ⟨25692734386156533716988173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17128489590771022477992115 25692734386156533716988173)
          ·
            refine ⟨9634775394808700143870565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25692734386156533716988173 9634775394808700143870565)
            ·
              refine ⟨1806520386526631276975731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9634775394808700143870565 1806520386526631276975731)
              ·
                refine ⟨2709780579789946915463597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806520386526631276975731 2709780579789946915463597)
                ·
                  refine ⟨1016167717421230093298849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2709780579789946915463597 1016167717421230093298849)
                  ·
                    refine ⟨762125788065922569974137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1016167717421230093298849 762125788065922569974137)
                    ·
                      refine ⟨571594341049441927480603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762125788065922569974137 571594341049441927480603)
                      ·
                        rfl

theorem cell23_1113176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_1113176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113176 prefixEnd_1113176 := by exact prefixLift 1113176
  have htrace : WordTrace (prefixWord ++ tailWord_1113176) baseStart_1113176 baseEnd_1113176 := by
    simpa [prefixWord, tailWord_1113176, baseEnd_1113176] using wordTrace_append hprefix tailTrace_1113176
  have hstable : (prefixWord ++ tailWord_1113176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113176).length < 2 ^ (prefixWord ++ tailWord_1113176).sum := by decide
  have hdescent : baseEnd_1113176 < baseStart_1113176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113186 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1113186 : Nat := 118140960795 + 1113186 * 2 ^ 59
def prefixEnd_1113186 : Nat := 4983230072969 + 3 ^ 40 * 1113186 * 2
def baseEnd_1113186 : Nat := 190533158618662296118519

theorem tailTrace_1113186 : CollatzResearch.WordTrace tailWord_1113186 prefixEnd_1113186 190533158618662296118519 := by
  unfold tailWord_1113186
  simp only [CollatzResearch.WordTrace]
  refine ⟨10150307236281178469479853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27067485963416475918612941 10150307236281178469479853)
  ·
    refine ⟨3806365213605441926054945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10150307236281178469479853 3806365213605441926054945)
    ·
      refine ⟨2854773910204081444541209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3806365213605441926054945 2854773910204081444541209)
      ·
        refine ⟨2141080432653061083405907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2854773910204081444541209 2141080432653061083405907)
        ·
          refine ⟨3211620648979591625108861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141080432653061083405907 3211620648979591625108861)
          ·
            refine ⟨1204357743367346859415823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3211620648979591625108861 1204357743367346859415823)
            ·
              refine ⟨1806536615051020289123735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204357743367346859415823 1806536615051020289123735)
              ·
                refine ⟨2709804922576530433685603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806536615051020289123735 2709804922576530433685603)
                ·
                  refine ⟨4064707383864795650528405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709804922576530433685603 4064707383864795650528405)
                  ·
                    refine ⟨190533158618662296118519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4064707383864795650528405 190533158618662296118519)
                    ·
                      rfl

theorem cell23_1113186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1113186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113186 prefixEnd_1113186 := by exact prefixLift 1113186
  have htrace : WordTrace (prefixWord ++ tailWord_1113186) baseStart_1113186 baseEnd_1113186 := by
    simpa [prefixWord, tailWord_1113186, baseEnd_1113186] using wordTrace_append hprefix tailTrace_1113186
  have hstable : (prefixWord ++ tailWord_1113186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113186).length < 2 ^ (prefixWord ++ tailWord_1113186).sum := by decide
  have hdescent : baseEnd_1113186 < baseStart_1113186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113215 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_1113215 : Nat := 118140960795 + 1113215 * 2 ^ 59
def prefixEnd_1113215 : Nat := 4983230072969 + 3 ^ 40 * 1113215 * 2
def baseEnd_1113215 : Nat := 571614366794967274892923

theorem tailTrace_1113215 : CollatzResearch.WordTrace tailWord_1113215 prefixEnd_1113215 571614366794967274892923 := by
  unfold tailWord_1113215
  simp only [CollatzResearch.WordTrace]
  refine ⟨40602286662019651830725099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27068191108013101220483399 40602286662019651830725099)
  ·
    refine ⟨60903429993029477746087649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40602286662019651830725099 60903429993029477746087649)
    ·
      refine ⟨45677572494772108309565737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60903429993029477746087649 45677572494772108309565737)
      ·
        refine ⟨34258179371079081232174303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45677572494772108309565737 34258179371079081232174303)
        ·
          refine ⟨51387269056618621848261455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34258179371079081232174303 51387269056618621848261455)
          ·
            refine ⟨77080903584927932772392183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51387269056618621848261455 77080903584927932772392183)
            ·
              refine ⟨115621355377391899158588275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77080903584927932772392183 115621355377391899158588275)
              ·
                refine ⟨173432033066087848737882413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115621355377391899158588275 173432033066087848737882413)
                ·
                  refine ⟨65037012399782943276705905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173432033066087848737882413 65037012399782943276705905)
                  ·
                    refine ⟨48777759299837207457529429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65037012399782943276705905 48777759299837207457529429)
                    ·
                      refine ⟨571614366794967274892923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 48777759299837207457529429 571614366794967274892923)
                      ·
                        rfl

theorem cell23_1113215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_1113215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113215 prefixEnd_1113215 := by exact prefixLift 1113215
  have htrace : WordTrace (prefixWord ++ tailWord_1113215) baseStart_1113215 baseEnd_1113215 := by
    simpa [prefixWord, tailWord_1113215, baseEnd_1113215] using wordTrace_append hprefix tailTrace_1113215
  have hstable : (prefixWord ++ tailWord_1113215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113215).length < 2 ^ (prefixWord ++ tailWord_1113215).sum := by decide
  have hdescent : baseEnd_1113215 < baseStart_1113215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113226 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1113226 : Nat := 118140960795 + 1113226 * 2 ^ 59
def prefixEnd_1113226 : Nat := 4983230072969 + 3 ^ 40 * 1113226 * 2
def baseEnd_1113226 : Nat := 571620015082166731855373

theorem tailTrace_1113226 : CollatzResearch.WordTrace tailWord_1113226 prefixEnd_1113226 571620015082166731855373 := by
  unfold tailWord_1113226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10150671966244950177343883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27068458576653200472917021 10150671966244950177343883)
  ·
    refine ⟨15226007949367425266015825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10150671966244950177343883 15226007949367425266015825)
    ·
      refine ⟨11419505962025568949511869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15226007949367425266015825 11419505962025568949511869)
      ·
        refine ⟨4282314735759588356066951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11419505962025568949511869 4282314735759588356066951)
        ·
          refine ⟨6423472103639382534100427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282314735759588356066951 6423472103639382534100427)
          ·
            refine ⟨9635208155459073801150641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423472103639382534100427 9635208155459073801150641)
            ·
              refine ⟨7226406116594305350862981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9635208155459073801150641 7226406116594305350862981)
              ·
                refine ⟨1354951146861432253286809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7226406116594305350862981 1354951146861432253286809)
                ·
                  refine ⟨1016213360146074189965107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1354951146861432253286809 1016213360146074189965107)
                  ·
                    refine ⟨1524320040219111284947661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1016213360146074189965107 1524320040219111284947661)
                    ·
                      refine ⟨571620015082166731855373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1524320040219111284947661 571620015082166731855373)
                      ·
                        rfl

theorem cell23_1113226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1113226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113226 prefixEnd_1113226 := by exact prefixLift 1113226
  have htrace : WordTrace (prefixWord ++ tailWord_1113226) baseStart_1113226 baseEnd_1113226 := by
    simpa [prefixWord, tailWord_1113226, baseEnd_1113226] using wordTrace_append hprefix tailTrace_1113226
  have hstable : (prefixWord ++ tailWord_1113226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113226).length < 2 ^ (prefixWord ++ tailWord_1113226).sum := by decide
  have hdescent : baseEnd_1113226 < baseStart_1113226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113253 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 1, 3, 2]
def baseStart_1113253 : Nat := 118140960795 + 1113253 * 2 ^ 59
def prefixEnd_1113253 : Nat := 4983230072969 + 3 ^ 40 * 1113253 * 2
def baseEnd_1113253 : Nat := 571633879059838126217749

theorem tailTrace_1113253 : CollatzResearch.WordTrace tailWord_1113253 prefixEnd_1113253 571633879059838126217749 := by
  unfold tailWord_1113253
  simp only [CollatzResearch.WordTrace]
  refine ⟨40603672635881984320608413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27069115090587989547072275 40603672635881984320608413)
  ·
    refine ⟨15226377238455744120228155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40603672635881984320608413 15226377238455744120228155)
    ·
      refine ⟨22839565857683616180342233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15226377238455744120228155 22839565857683616180342233)
      ·
        refine ⟨17129674393262712135256675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22839565857683616180342233 17129674393262712135256675)
        ·
          refine ⟨25694511589894068202885013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17129674393262712135256675 25694511589894068202885013)
          ·
            refine ⟨1204430230776284447010235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25694511589894068202885013 1204430230776284447010235)
            ·
              refine ⟨1806645346164426670515353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204430230776284447010235 1806645346164426670515353)
              ·
                refine ⟨1354984009623320002886515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1806645346164426670515353 1354984009623320002886515)
                ·
                  refine ⟨2032476014434980004329773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354984009623320002886515 2032476014434980004329773)
                  ·
                    refine ⟨762178505413117501623665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2032476014434980004329773 762178505413117501623665)
                    ·
                      refine ⟨571633879059838126217749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762178505413117501623665 571633879059838126217749)
                      ·
                        rfl

theorem cell23_1113253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_1113253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113253 prefixEnd_1113253 := by exact prefixLift 1113253
  have htrace : WordTrace (prefixWord ++ tailWord_1113253) baseStart_1113253 baseEnd_1113253 := by
    simpa [prefixWord, tailWord_1113253, baseEnd_1113253] using wordTrace_append hprefix tailTrace_1113253
  have hstable : (prefixWord ++ tailWord_1113253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113253).length < 2 ^ (prefixWord ++ tailWord_1113253).sum := by decide
  have hdescent : baseEnd_1113253 < baseStart_1113253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113266 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_1113266 : Nat := 118140960795 + 1113266 * 2 ^ 59
def prefixEnd_1113266 : Nat := 4983230072969 + 3 ^ 40 * 1113266 * 2
def baseEnd_1113266 : Nat := 571640554308346575355189

theorem tailTrace_1113266 : CollatzResearch.WordTrace tailWord_1113266 prefixEnd_1113266 571640554308346575355189 := by
  unfold tailWord_1113266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10151036696208721885207913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27069431189889925027221101 10151036696208721885207913)
  ·
    refine ⟨7613277522156541413905935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10151036696208721885207913 7613277522156541413905935)
    ·
      refine ⟨11419916283234812120858903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7613277522156541413905935 11419916283234812120858903)
      ·
        refine ⟨17129874424852218181288355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11419916283234812120858903 17129874424852218181288355)
        ·
          refine ⟨25694811637278327271932533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17129874424852218181288355 25694811637278327271932533)
          ·
            refine ⟨2408888590994843181743675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25694811637278327271932533 2408888590994843181743675)
            ·
              refine ⟨3613332886492264772615513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408888590994843181743675 3613332886492264772615513)
              ·
                refine ⟨2709999664869198579461635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3613332886492264772615513 2709999664869198579461635)
                ·
                  refine ⟨4064999497303797869192453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709999664869198579461635 4064999497303797869192453)
                  ·
                    refine ⟨762187405744462100473585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4064999497303797869192453 762187405744462100473585)
                    ·
                      refine ⟨571640554308346575355189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762187405744462100473585 571640554308346575355189)
                      ·
                        rfl

theorem cell23_1113266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_1113266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113266 prefixEnd_1113266 := by exact prefixLift 1113266
  have htrace : WordTrace (prefixWord ++ tailWord_1113266) baseStart_1113266 baseEnd_1113266 := by
    simpa [prefixWord, tailWord_1113266, baseEnd_1113266] using wordTrace_append hprefix tailTrace_1113266
  have hstable : (prefixWord ++ tailWord_1113266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113266).length < 2 ^ (prefixWord ++ tailWord_1113266).sum := by decide
  have hdescent : baseEnd_1113266 < baseStart_1113266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113293 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1113293 : Nat := 118140960795 + 1113293 * 2 ^ 59
def prefixEnd_1113293 : Nat := 4983230072969 + 3 ^ 40 * 1113293 * 2
def baseEnd_1113293 : Nat := 190551472762005989905855

theorem tailTrace_1113293 : CollatzResearch.WordTrace tailWord_1113293 prefixEnd_1113293 190551472762005989905855 := by
  unfold tailWord_1113293
  simp only [CollatzResearch.WordTrace]
  refine ⟨40605131555737071152064533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27070087703824714101376355 40605131555737071152064533)
  ·
    refine ⟨1903365541675175210253025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40605131555737071152064533 1903365541675175210253025)
    ·
      refine ⟨1427524156256381407689769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1903365541675175210253025 1427524156256381407689769)
      ·
        refine ⟨1070643117192286055767327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1427524156256381407689769 1070643117192286055767327)
        ·
          refine ⟨1605964675788429083650991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070643117192286055767327 1605964675788429083650991)
          ·
            refine ⟨2408947013682643625476487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605964675788429083650991 2408947013682643625476487)
            ·
              refine ⟨3613420520523965438214731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408947013682643625476487 3613420520523965438214731)
              ·
                refine ⟨5420130780785948157322097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613420520523965438214731 5420130780785948157322097)
                ·
                  refine ⟨4065098085589461117991573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5420130780785948157322097 4065098085589461117991573)
                  ·
                    refine ⟨190551472762005989905855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4065098085589461117991573 190551472762005989905855)
                    ·
                      rfl

theorem cell23_1113293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1113293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113293 prefixEnd_1113293 := by exact prefixLift 1113293
  have htrace : WordTrace (prefixWord ++ tailWord_1113293) baseStart_1113293 baseEnd_1113293 := by
    simpa [prefixWord, tailWord_1113293, baseEnd_1113293] using wordTrace_append hprefix tailTrace_1113293
  have hstable : (prefixWord ++ tailWord_1113293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113293).length < 2 ^ (prefixWord ++ tailWord_1113293).sum := by decide
  have hdescent : baseEnd_1113293 < baseStart_1113293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113300 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1113300 : Nat := 118140960795 + 1113300 * 2 ^ 59
def prefixEnd_1113300 : Nat := 4983230072969 + 3 ^ 40 * 1113300 * 2
def baseEnd_1113300 : Nat := 571658012650599442330033

theorem tailTrace_1113300 : CollatzResearch.WordTrace tailWord_1113300 prefixEnd_1113300 571658012650599442330033 := by
  unfold tailWord_1113300
  simp only [CollatzResearch.WordTrace]
  refine ⟨20302693433355855673784677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27070257911141140898379569 20302693433355855673784677)
  ·
    refine ⟨3806755018754222938834627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20302693433355855673784677 3806755018754222938834627)
    ·
      refine ⟨5710132528131334408251941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3806755018754222938834627 5710132528131334408251941)
      ·
        refine ⟨1070649849024625201547239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5710132528131334408251941 1070649849024625201547239)
        ·
          refine ⟨1605974773536937802320859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070649849024625201547239 1605974773536937802320859)
          ·
            refine ⟨2408962160305406703481289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605974773536937802320859 2408962160305406703481289)
            ·
              refine ⟨1806721620229055027610967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408962160305406703481289 1806721620229055027610967)
              ·
                refine ⟨2710082430343582541416451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806721620229055027610967 2710082430343582541416451)
                ·
                  refine ⟨4065123645515373812124677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710082430343582541416451 4065123645515373812124677)
                  ·
                    refine ⟨762210683534132589773377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065123645515373812124677 762210683534132589773377)
                    ·
                      refine ⟨571658012650599442330033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762210683534132589773377 571658012650599442330033)
                      ·
                        rfl

theorem cell23_1113300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1113300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113300 prefixEnd_1113300 := by exact prefixLift 1113300
  have htrace : WordTrace (prefixWord ++ tailWord_1113300) baseStart_1113300 baseEnd_1113300 := by
    simpa [prefixWord, tailWord_1113300, baseEnd_1113300] using wordTrace_append hprefix tailTrace_1113300
  have hstable : (prefixWord ++ tailWord_1113300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113300).length < 2 ^ (prefixWord ++ tailWord_1113300).sum := by decide
  have hdescent : baseEnd_1113300 < baseStart_1113300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113356 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 2, 4, 2]
def baseStart_1113356 : Nat := 118140960795 + 1113356 * 2 ^ 59
def prefixEnd_1113356 : Nat := 4983230072969 + 3 ^ 40 * 1113356 * 2
def baseEnd_1113356 : Nat := 571686767567251223229775

theorem tailTrace_1113356 : CollatzResearch.WordTrace tailWord_1113356 prefixEnd_1113356 571686767567251223229775 := by
  unfold tailWord_1113356
  simp only [CollatzResearch.WordTrace]
  refine ⟨20303714677254416455803961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27071619569672555274405281 20303714677254416455803961)
  ·
    refine ⟨15227786007940812341852971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20303714677254416455803961 15227786007940812341852971)
    ·
      refine ⟨22841679011911218512779457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15227786007940812341852971 22841679011911218512779457)
      ·
        refine ⟨17131259258933413884584593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22841679011911218512779457 17131259258933413884584593)
        ·
          refine ⟨12848444444200060413438445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17131259258933413884584593 12848444444200060413438445)
          ·
            refine ⟨4818166666575022655039417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12848444444200060413438445 4818166666575022655039417)
            ·
              refine ⟨3613624999931266991279563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4818166666575022655039417 3613624999931266991279563)
              ·
                refine ⟨5420437499896900486919345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613624999931266991279563 5420437499896900486919345)
                ·
                  refine ⟨4065328124922675365189509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5420437499896900486919345 4065328124922675365189509)
                  ·
                    refine ⟨762249023423001630973033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065328124922675365189509 762249023423001630973033)
                    ·
                      refine ⟨571686767567251223229775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762249023423001630973033 571686767567251223229775)
                      ·
                        rfl

theorem cell23_1113356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_1113356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113356 prefixEnd_1113356 := by exact prefixLift 1113356
  have htrace : WordTrace (prefixWord ++ tailWord_1113356) baseStart_1113356 baseEnd_1113356 := by
    simpa [prefixWord, tailWord_1113356, baseEnd_1113356] using wordTrace_append hprefix tailTrace_1113356
  have hstable : (prefixWord ++ tailWord_1113356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113356).length < 2 ^ (prefixWord ++ tailWord_1113356).sum := by decide
  have hdescent : baseEnd_1113356 < baseStart_1113356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113396 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 6]
def baseStart_1113396 : Nat := 118140960795 + 1113396 * 2 ^ 59
def prefixEnd_1113396 : Nat := 4983230072969 + 3 ^ 40 * 1113396 * 2
def baseEnd_1113396 : Nat := 63523034088159007414399

theorem tailTrace_1113396 : CollatzResearch.WordTrace tailWord_1113396 prefixEnd_1113396 63523034088159007414399 := by
  unfold tailWord_1113396
  simp only [CollatzResearch.WordTrace]
  refine ⟨20304444137181959871532021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27072592182909279828709361 20304444137181959871532021)
  ·
    refine ⟨1903541637860808737956127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20304444137181959871532021 1903541637860808737956127)
    ·
      refine ⟨2855312456791213106934191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903541637860808737956127 2855312456791213106934191)
      ·
        refine ⟨4282968685186819660401287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2855312456791213106934191 4282968685186819660401287)
        ·
          refine ⟨6424453027780229490601931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282968685186819660401287 6424453027780229490601931)
          ·
            refine ⟨9636679541670344235902897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6424453027780229490601931 9636679541670344235902897)
            ·
              refine ⟨7227509656252758176927173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9636679541670344235902897 7227509656252758176927173)
              ·
                refine ⟨1355158060547392158173845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7227509656252758176927173 1355158060547392158173845)
                ·
                  refine ⟨63523034088159007414399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1355158060547392158173845 63523034088159007414399)
                  ·
                    rfl

theorem cell23_1113396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_1113396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113396 prefixEnd_1113396 := by exact prefixLift 1113396
  have htrace : WordTrace (prefixWord ++ tailWord_1113396) baseStart_1113396 baseEnd_1113396 := by
    simpa [prefixWord, tailWord_1113396, baseEnd_1113396] using wordTrace_append hprefix tailTrace_1113396
  have hstable : (prefixWord ++ tailWord_1113396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113396).length < 2 ^ (prefixWord ++ tailWord_1113396).sum := by decide
  have hdescent : baseEnd_1113396 < baseStart_1113396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113416 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_1113416 : Nat := 118140960795 + 1113416 * 2 ^ 59
def prefixEnd_1113416 : Nat := 4983230072969 + 3 ^ 40 * 1113416 * 2
def baseEnd_1113416 : Nat := 571717576406520988479499

theorem tailTrace_1113416 : CollatzResearch.WordTrace tailWord_1113416 prefixEnd_1113416 571717576406520988479499 := by
  unfold tailWord_1113416
  simp only [CollatzResearch.WordTrace]
  refine ⟨20304808867145731579396051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27073078489527642105861401 20304808867145731579396051)
  ·
    refine ⟨30457213300718597369094077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20304808867145731579396051 30457213300718597369094077)
    ·
      refine ⟨11421454987769474013410279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30457213300718597369094077 11421454987769474013410279)
      ·
        refine ⟨17132182481654211020115419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11421454987769474013410279 17132182481654211020115419)
        ·
          refine ⟨25698273722481316530173129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17132182481654211020115419 25698273722481316530173129)
          ·
            refine ⟨19273705291860987397629847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25698273722481316530173129 19273705291860987397629847)
            ·
              refine ⟨28910557937791481096444771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19273705291860987397629847 28910557937791481096444771)
              ·
                refine ⟨43365836906687221644667157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28910557937791481096444771 43365836906687221644667157)
                ·
                  refine ⟨2032773605000963514593773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43365836906687221644667157 2032773605000963514593773)
                  ·
                    refine ⟨762290101875361317972665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2032773605000963514593773 762290101875361317972665)
                    ·
                      refine ⟨571717576406520988479499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762290101875361317972665 571717576406520988479499)
                      ·
                        rfl

theorem cell23_1113416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_1113416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113416 prefixEnd_1113416 := by exact prefixLift 1113416
  have htrace : WordTrace (prefixWord ++ tailWord_1113416) baseStart_1113416 baseEnd_1113416 := by
    simpa [prefixWord, tailWord_1113416, baseEnd_1113416] using wordTrace_append hprefix tailTrace_1113416
  have hstable : (prefixWord ++ tailWord_1113416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113416).length < 2 ^ (prefixWord ++ tailWord_1113416).sum := by decide
  have hdescent : baseEnd_1113416 < baseStart_1113416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113443 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 1, 5]
def baseStart_1113443 : Nat := 118140960795 + 1113443 * 2 ^ 59
def prefixEnd_1113443 : Nat := 4983230072969 + 3 ^ 40 * 1113443 * 2
def baseEnd_1113443 : Nat := 190577146794730794280625

theorem tailTrace_1113443 : CollatzResearch.WordTrace tailWord_1113443 prefixEnd_1113443 190577146794730794280625 := by
  unfold tailWord_1113443
  simp only [CollatzResearch.WordTrace]
  refine ⟨40610602505193646770024983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27073735003462431180016655 40610602505193646770024983)
  ·
    refine ⟨60915903757790470155037475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40610602505193646770024983 60915903757790470155037475)
    ·
      refine ⟨91373855636685705232556213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60915903757790470155037475 91373855636685705232556213)
      ·
        refine ⟨8566298965939284865552145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91373855636685705232556213 8566298965939284865552145)
        ·
          refine ⟨6424724224454463649164109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8566298965939284865552145 6424724224454463649164109)
          ·
            refine ⟨2409271584170423868436541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6424724224454463649164109 2409271584170423868436541)
            ·
              refine ⟨903476844063908950663703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2409271584170423868436541 903476844063908950663703)
              ·
                refine ⟨1355215266095863425995555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903476844063908950663703 1355215266095863425995555)
                ·
                  refine ⟨2032822899143795138993333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355215266095863425995555 2032822899143795138993333)
                  ·
                    refine ⟨190577146794730794280625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2032822899143795138993333 190577146794730794280625)
                    ·
                      rfl

theorem cell23_1113443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 5].length) (baseStart_1113443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113443 prefixEnd_1113443 := by exact prefixLift 1113443
  have htrace : WordTrace (prefixWord ++ tailWord_1113443) baseStart_1113443 baseEnd_1113443 := by
    simpa [prefixWord, tailWord_1113443, baseEnd_1113443] using wordTrace_append hprefix tailTrace_1113443
  have hstable : (prefixWord ++ tailWord_1113443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113443).length < 2 ^ (prefixWord ++ tailWord_1113443).sum := by decide
  have hdescent : baseEnd_1113443 < baseStart_1113443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113449 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_1113449 : Nat := 118140960795 + 1113449 * 2 ^ 59
def prefixEnd_1113449 : Nat := 4983230072969 + 3 ^ 40 * 1113449 * 2
def baseEnd_1113449 : Nat := 571734521268119359366847

theorem tailTrace_1113449 : CollatzResearch.WordTrace tailWord_1113449 prefixEnd_1113449 571734521268119359366847 := by
  unfold tailWord_1113449
  simp only [CollatzResearch.WordTrace]
  refine ⟨40610821343171909794743401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27073880895447939863162267 40610821343171909794743401)
  ·
    refine ⟨30458116007378932346057551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40610821343171909794743401 30458116007378932346057551)
    ·
      refine ⟨45687174011068398519086327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30458116007378932346057551 45687174011068398519086327)
      ·
        refine ⟨68530761016602597778629491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45687174011068398519086327 68530761016602597778629491)
        ·
          refine ⟨102796141524903896667944237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68530761016602597778629491 102796141524903896667944237)
          ·
            refine ⟨38548553071838961250479089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102796141524903896667944237 38548553071838961250479089)
            ·
              refine ⟨28911414803879220937859317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38548553071838961250479089 28911414803879220937859317)
              ·
                refine ⟨2710445137863676962924311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28911414803879220937859317 2710445137863676962924311)
                ·
                  refine ⟨4065667706795515444386467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710445137863676962924311 4065667706795515444386467)
                  ·
                    refine ⟨6098501560193273166579701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4065667706795515444386467 6098501560193273166579701)
                    ·
                      refine ⟨571734521268119359366847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6098501560193273166579701 571734521268119359366847)
                      ·
                        rfl

theorem cell23_1113449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_1113449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113449 prefixEnd_1113449 := by exact prefixLift 1113449
  have htrace : WordTrace (prefixWord ++ tailWord_1113449) baseStart_1113449 baseEnd_1113449 := by
    simpa [prefixWord, tailWord_1113449, baseEnd_1113449] using wordTrace_append hprefix tailTrace_1113449
  have hstable : (prefixWord ++ tailWord_1113449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113449).length < 2 ^ (prefixWord ++ tailWord_1113449).sum := by decide
  have hdescent : baseEnd_1113449 < baseStart_1113449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113463 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 3, 2, 2]
def baseStart_1113463 : Nat := 118140960795 + 1113463 * 2 ^ 59
def prefixEnd_1113463 : Nat := 4983230072969 + 3 ^ 40 * 1113463 * 2
def baseEnd_1113463 : Nat := 571741709997282304591783

theorem tailTrace_1113463 : CollatzResearch.WordTrace tailWord_1113463 prefixEnd_1113463 571741709997282304591783 := by
  unfold tailWord_1113463
  simp only [CollatzResearch.WordTrace]
  refine ⟨40611331965121190185753043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27074221310080793457168695 40611331965121190185753043)
  ·
    refine ⟨60916997947681785278629565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40611331965121190185753043 60916997947681785278629565)
    ·
      refine ⟨22843874230380669479486087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60916997947681785278629565 22843874230380669479486087)
      ·
        refine ⟨34265811345571004219229131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22843874230380669479486087 34265811345571004219229131)
        ·
          refine ⟨51398717018356506328843697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34265811345571004219229131 51398717018356506328843697)
          ·
            refine ⟨38549037763767379746632773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51398717018356506328843697 38549037763767379746632773)
            ·
              refine ⟨7227944580706383702493645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38549037763767379746632773 7227944580706383702493645)
              ·
                refine ⟨2710479217764893888435117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7227944580706383702493645 2710479217764893888435117)
                ·
                  refine ⟨1016429706661835208163169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2710479217764893888435117 1016429706661835208163169)
                  ·
                    refine ⟨762322279996376406122377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1016429706661835208163169 762322279996376406122377)
                    ·
                      refine ⟨571741709997282304591783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762322279996376406122377 571741709997282304591783)
                      ·
                        rfl

theorem cell23_1113463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_1113463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113463 prefixEnd_1113463 := by exact prefixLift 1113463
  have htrace : WordTrace (prefixWord ++ tailWord_1113463) baseStart_1113463 baseEnd_1113463 := by
    simpa [prefixWord, tailWord_1113463, baseEnd_1113463] using wordTrace_append hprefix tailTrace_1113463
  have hstable : (prefixWord ++ tailWord_1113463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113463).length < 2 ^ (prefixWord ++ tailWord_1113463).sum := by decide
  have hdescent : baseEnd_1113463 < baseStart_1113463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113473 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1113473 : Nat := 118140960795 + 1113473 * 2 ^ 59
def prefixEnd_1113473 : Nat := 4983230072969 + 3 ^ 40 * 1113473 * 2
def baseEnd_1113473 : Nat := 190582281601275755155579

theorem tailTrace_1113473 : CollatzResearch.WordTrace tailWord_1113473 prefixEnd_1113473 190582281601275755155579 := by
  unfold tailWord_1113473
  simp only [CollatzResearch.WordTrace]
  refine ⟨40611696695084961893617073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27074464463389974595744715 40611696695084961893617073)
  ·
    refine ⟨30458772521313721420212805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40611696695084961893617073 30458772521313721420212805)
    ·
      refine ⟨5711019847746322766289901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30458772521313721420212805 5711019847746322766289901)
      ·
        refine ⟨2141632442904871037358713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5711019847746322766289901 2141632442904871037358713)
        ·
          refine ⟨1606224332178653278019035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2141632442904871037358713 1606224332178653278019035)
          ·
            refine ⟨2409336498267979917028553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606224332178653278019035 2409336498267979917028553)
            ·
              refine ⟨1807002373700984937771415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2409336498267979917028553 1807002373700984937771415)
              ·
                refine ⟨2710503560551477406657123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807002373700984937771415 2710503560551477406657123)
                ·
                  refine ⟨4065755340827216109985685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710503560551477406657123 4065755340827216109985685)
                  ·
                    refine ⟨190582281601275755155579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4065755340827216109985685 190582281601275755155579)
                    ·
                      rfl

theorem cell23_1113473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1113473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113473 prefixEnd_1113473 := by exact prefixLift 1113473
  have htrace : WordTrace (prefixWord ++ tailWord_1113473) baseStart_1113473 baseEnd_1113473 := by
    simpa [prefixWord, tailWord_1113473, baseEnd_1113473] using wordTrace_append hprefix tailTrace_1113473
  have hstable : (prefixWord ++ tailWord_1113473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113473).length < 2 ^ (prefixWord ++ tailWord_1113473).sum := by decide
  have hdescent : baseEnd_1113473 < baseStart_1113473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113476 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1113476 : Nat := 118140960795 + 1113476 * 2 ^ 59
def prefixEnd_1113476 : Nat := 4983230072969 + 3 ^ 40 * 1113476 * 2
def baseEnd_1113476 : Nat := 571748385245790753729223

theorem tailTrace_1113476 : CollatzResearch.WordTrace tailWord_1113476 prefixEnd_1113476 571748385245790753729223 := by
  unfold tailWord_1113476
  simp only [CollatzResearch.WordTrace]
  refine ⟨20305903057037046702988141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27074537409382728937317521 20305903057037046702988141)
  ·
    refine ⟨7614713646388892513620553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20305903057037046702988141 7614713646388892513620553)
    ·
      refine ⟨5711035234791669385215415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7614713646388892513620553 5711035234791669385215415)
      ·
        refine ⟨8566552852187504077823123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5711035234791669385215415 8566552852187504077823123)
        ·
          refine ⟨12849829278281256116734685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8566552852187504077823123 12849829278281256116734685)
          ·
            refine ⟨4818685979355471043775507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12849829278281256116734685 4818685979355471043775507)
            ·
              refine ⟨7228028969033206565663261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818685979355471043775507 7228028969033206565663261)
              ·
                refine ⟨2710510863387452462123723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7228028969033206565663261 2710510863387452462123723)
                ·
                  refine ⟨4065766295081178693185585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710510863387452462123723 4065766295081178693185585)
                  ·
                    refine ⟨3049324721310884019889189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4065766295081178693185585 3049324721310884019889189)
                    ·
                      refine ⟨571748385245790753729223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3049324721310884019889189 571748385245790753729223)
                      ·
                        rfl

theorem cell23_1113476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1113476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113476 prefixEnd_1113476 := by exact prefixLift 1113476
  have htrace : WordTrace (prefixWord ++ tailWord_1113476) baseStart_1113476 baseEnd_1113476 := by
    simpa [prefixWord, tailWord_1113476, baseEnd_1113476] using wordTrace_append hprefix tailTrace_1113476
  have hstable : (prefixWord ++ tailWord_1113476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113476).length < 2 ^ (prefixWord ++ tailWord_1113476).sum := by decide
  have hdescent : baseEnd_1113476 < baseStart_1113476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113480 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_1113480 : Nat := 118140960795 + 1113480 * 2 ^ 59
def prefixEnd_1113480 : Nat := 4983230072969 + 3 ^ 40 * 1113480 * 2
def baseEnd_1113480 : Nat := 571750439168408738079205

theorem tailTrace_1113480 : CollatzResearch.WordTrace tailWord_1113480 prefixEnd_1113480 571750439168408738079205 := by
  unfold tailWord_1113480
  simp only [CollatzResearch.WordTrace]
  refine ⟨20305976003029801044560947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27074634670706401392747929 20305976003029801044560947)
  ·
    refine ⟨30458964004544701566841421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20305976003029801044560947 30458964004544701566841421)
    ·
      refine ⟨11422111501704263087565533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30458964004544701566841421 11422111501704263087565533)
      ·
        refine ⟨4283291813139098657837075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11422111501704263087565533 4283291813139098657837075)
        ·
          refine ⟨6424937719708647986755613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283291813139098657837075 6424937719708647986755613)
          ·
            refine ⟨2409351644890742995033355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6424937719708647986755613 2409351644890742995033355)
            ·
              refine ⟨3614027467336114492550033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2409351644890742995033355 3614027467336114492550033)
              ·
                refine ⟨2710520600502085869412525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3614027467336114492550033 2710520600502085869412525)
                ·
                  refine ⟨1016445225188282201029697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2710520600502085869412525 1016445225188282201029697)
                  ·
                    refine ⟨762333918891211650772273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1016445225188282201029697 762333918891211650772273)
                    ·
                      refine ⟨571750439168408738079205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762333918891211650772273 571750439168408738079205)
                      ·
                        rfl

theorem cell23_1113480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_1113480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113480 prefixEnd_1113480 := by exact prefixLift 1113480
  have htrace : WordTrace (prefixWord ++ tailWord_1113480) baseStart_1113480 baseEnd_1113480 := by
    simpa [prefixWord, tailWord_1113480, baseEnd_1113480] using wordTrace_append hprefix tailTrace_1113480
  have hstable : (prefixWord ++ tailWord_1113480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113480).length < 2 ^ (prefixWord ++ tailWord_1113480).sum := by decide
  have hdescent : baseEnd_1113480 < baseStart_1113480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113497 : List Nat := [1, 2, 1, 2, 1, 6, 2, 3, 1, 2, 2]
def baseStart_1113497 : Nat := 118140960795 + 1113497 * 2 ^ 59
def prefixEnd_1113497 : Nat := 4983230072969 + 3 ^ 40 * 1113497 * 2
def baseEnd_1113497 : Nat := 571759168339535171566627

theorem tailTrace_1113497 : CollatzResearch.WordTrace tailWord_1113497 prefixEnd_1113497 571759168339535171566627 := by
  unfold tailWord_1113497
  simp only [CollatzResearch.WordTrace]
  refine ⟨40612572046998013992490745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27075048031332009328327163 40612572046998013992490745)
  ·
    refine ⟨30459429035248510494368059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40612572046998013992490745 30459429035248510494368059)
    ·
      refine ⟨45689143552872765741552089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30459429035248510494368059 45689143552872765741552089)
      ·
        refine ⟨34266857664654574306164067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45689143552872765741552089 34266857664654574306164067)
        ·
          refine ⟨51400286496981861459246101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34266857664654574306164067 51400286496981861459246101)
          ·
            refine ⟨2409388429546024755902161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51400286496981861459246101 2409388429546024755902161)
            ·
              refine ⟨1807041322159518566926621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2409388429546024755902161 1807041322159518566926621)
              ·
                refine ⟨677640495809819462597483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1807041322159518566926621 677640495809819462597483)
                ·
                  refine ⟨1016460743714729193896225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677640495809819462597483 1016460743714729193896225)
                  ·
                    refine ⟨762345557786046895422169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1016460743714729193896225 762345557786046895422169)
                    ·
                      refine ⟨571759168339535171566627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762345557786046895422169 571759168339535171566627)
                      ·
                        rfl

theorem cell23_1113497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_1113497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113497 prefixEnd_1113497 := by exact prefixLift 1113497
  have htrace : WordTrace (prefixWord ++ tailWord_1113497) baseStart_1113497 baseEnd_1113497 := by
    simpa [prefixWord, tailWord_1113497, baseEnd_1113497] using wordTrace_append hprefix tailTrace_1113497
  have hstable : (prefixWord ++ tailWord_1113497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113497).length < 2 ^ (prefixWord ++ tailWord_1113497).sum := by decide
  have hdescent : baseEnd_1113497 < baseStart_1113497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113509 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_1113509 : Nat := 118140960795 + 1113509 * 2 ^ 59
def prefixEnd_1113509 : Nat := 4983230072969 + 3 ^ 40 * 1113509 * 2
def baseEnd_1113509 : Nat := 571765330107389124616571

theorem tailTrace_1113509 : CollatzResearch.WordTrace tailWord_1113509 prefixEnd_1113509 571765330107389124616571 := by
  unfold tailWord_1113509
  simp only [CollatzResearch.WordTrace]
  refine ⟨40613009722954540041927581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27075339815303026694618387 40613009722954540041927581)
  ·
    refine ⟨15229878646107952515722843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40613009722954540041927581 15229878646107952515722843)
    ·
      refine ⟨22844817969161928773584265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15229878646107952515722843 22844817969161928773584265)
      ·
        refine ⟨17133613476871446580188199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22844817969161928773584265 17133613476871446580188199)
        ·
          refine ⟨25700420215307169870282299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17133613476871446580188199 25700420215307169870282299)
          ·
            refine ⟨38550630322960754805423449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25700420215307169870282299 38550630322960754805423449)
            ·
              refine ⟨28912972742220566104067587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38550630322960754805423449 28912972742220566104067587)
              ·
                refine ⟨43369459113330849156101381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28912972742220566104067587 43369459113330849156101381)
                ·
                  refine ⟨8131773583749534216769009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43369459113330849156101381 8131773583749534216769009)
                  ·
                    refine ⟨6098830187812150662576757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8131773583749534216769009 6098830187812150662576757)
                    ·
                      refine ⟨571765330107389124616571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6098830187812150662576757 571765330107389124616571)
                      ·
                        rfl

theorem cell23_1113509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_1113509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113509 prefixEnd_1113509 := by exact prefixLift 1113509
  have htrace : WordTrace (prefixWord ++ tailWord_1113509) baseStart_1113509 baseEnd_1113509 := by
    simpa [prefixWord, tailWord_1113509, baseEnd_1113509] using wordTrace_append hprefix tailTrace_1113509
  have hstable : (prefixWord ++ tailWord_1113509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113509).length < 2 ^ (prefixWord ++ tailWord_1113509).sum := by decide
  have hdescent : baseEnd_1113509 < baseStart_1113509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113519 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_1113519 : Nat := 118140960795 + 1113519 * 2 ^ 59
def prefixEnd_1113519 : Nat := 4983230072969 + 3 ^ 40 * 1113519 * 2
def baseEnd_1113519 : Nat := 571770464913934085491525

theorem tailTrace_1113519 : CollatzResearch.WordTrace tailWord_1113519 prefixEnd_1113519 571770464913934085491525 := by
  unfold tailWord_1113519
  simp only [CollatzResearch.WordTrace]
  refine ⟨40613374452918311749791611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27075582968612207833194407 40613374452918311749791611)
  ·
    refine ⟨60920061679377467624687417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40613374452918311749791611 60920061679377467624687417)
    ·
      refine ⟨45690046259533100718515563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60920061679377467624687417 45690046259533100718515563)
      ·
        refine ⟨68535069389299651077773345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45690046259533100718515563 68535069389299651077773345)
        ·
          refine ⟨51401302041974738308330009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68535069389299651077773345 51401302041974738308330009)
          ·
            refine ⟨38550976531481053731247507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51401302041974738308330009 38550976531481053731247507)
            ·
              refine ⟨57826464797221580596871261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38550976531481053731247507 57826464797221580596871261)
              ·
                refine ⟨21684924298958092723826723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57826464797221580596871261 21684924298958092723826723)
                ·
                  refine ⟨32527386448437139085740085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21684924298958092723826723 32527386448437139085740085)
                  ·
                    refine ⟨3049442479540981789288133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32527386448437139085740085 3049442479540981789288133)
                    ·
                      refine ⟨571770464913934085491525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3049442479540981789288133 571770464913934085491525)
                      ·
                        rfl

theorem cell23_1113519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_1113519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113519 prefixEnd_1113519 := by exact prefixLift 1113519
  have htrace : WordTrace (prefixWord ++ tailWord_1113519) baseStart_1113519 baseEnd_1113519 := by
    simpa [prefixWord, tailWord_1113519, baseEnd_1113519] using wordTrace_append hprefix tailTrace_1113519
  have hstable : (prefixWord ++ tailWord_1113519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113519).length < 2 ^ (prefixWord ++ tailWord_1113519).sum := by decide
  have hdescent : baseEnd_1113519 < baseStart_1113519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113559 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 9]
def baseStart_1113559 : Nat := 118140960795 + 1113559 * 2 ^ 59
def prefixEnd_1113559 : Nat := 4983230072969 + 3 ^ 40 * 1113559 * 2
def baseEnd_1113559 : Nat := 63532333793345992110149

theorem tailTrace_1113559 : CollatzResearch.WordTrace tailWord_1113559 prefixEnd_1113559 63532333793345992110149 := by
  unfold tailWord_1113559
  simp only [CollatzResearch.WordTrace]
  refine ⟨40614833372773398581247731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27076555581848932387498487 40614833372773398581247731)
  ·
    refine ⟨60922250059160097871871597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40614833372773398581247731 60922250059160097871871597)
    ·
      refine ⟨22845843772185036701951849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60922250059160097871871597 22845843772185036701951849)
      ·
        refine ⟨17134382829138777526463887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22845843772185036701951849 17134382829138777526463887)
        ·
          refine ⟨25701574243708166289695831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17134382829138777526463887 25701574243708166289695831)
          ·
            refine ⟨38552361365562249434543747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25701574243708166289695831 38552361365562249434543747)
            ·
              refine ⟨57828542048343374151815621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38552361365562249434543747 57828542048343374151815621)
              ·
                refine ⟨10842851634064382653465429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57828542048343374151815621 10842851634064382653465429)
                ·
                  refine ⟨63532333793345992110149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10842851634064382653465429 63532333793345992110149)
                  ·
                    rfl

theorem cell23_1113559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 9].length) (baseStart_1113559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113559 prefixEnd_1113559 := by exact prefixLift 1113559
  have htrace : WordTrace (prefixWord ++ tailWord_1113559) baseStart_1113559 baseEnd_1113559 := by
    simpa [prefixWord, tailWord_1113559, baseEnd_1113559] using wordTrace_append hprefix tailTrace_1113559
  have hstable : (prefixWord ++ tailWord_1113559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113559).length < 2 ^ (prefixWord ++ tailWord_1113559).sum := by decide
  have hdescent : baseEnd_1113559 < baseStart_1113559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113579 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 8]
def baseStart_1113579 : Nat := 118140960795 + 1113579 * 2 ^ 59
def prefixEnd_1113579 : Nat := 4983230072969 + 3 ^ 40 * 1113579 * 2
def baseEnd_1113579 : Nat := 571801273753203850741249

theorem tailTrace_1113579 : CollatzResearch.WordTrace tailWord_1113579 prefixEnd_1113579 571801273753203850741249 := by
  unfold tailWord_1113579
  simp only [CollatzResearch.WordTrace]
  refine ⟨40615562832700941996975791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27077041888467294664650527 40615562832700941996975791)
  ·
    refine ⟨60923344249051412995463687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40615562832700941996975791 60923344249051412995463687)
    ·
      refine ⟨91385016373577119493195531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60923344249051412995463687 91385016373577119493195531)
      ·
        refine ⟨137077524560365679239793297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91385016373577119493195531 137077524560365679239793297)
        ·
          refine ⟨102808143420274259429844973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137077524560365679239793297 102808143420274259429844973)
          ·
            refine ⟨38553053782602847286191865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102808143420274259429844973 38553053782602847286191865)
            ·
              refine ⟨28914790336952135464643899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38553053782602847286191865 28914790336952135464643899)
              ·
                refine ⟨43372185505428203196965849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28914790336952135464643899 43372185505428203196965849)
                ·
                  refine ⟨32529139129071152397724387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43372185505428203196965849 32529139129071152397724387)
                  ·
                    refine ⟨48793708693606728596586581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32529139129071152397724387 48793708693606728596586581)
                    ·
                      refine ⟨571801273753203850741249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 48793708693606728596586581 571801273753203850741249)
                      ·
                        rfl

theorem cell23_1113579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_1113579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113579 prefixEnd_1113579 := by exact prefixLift 1113579
  have htrace : WordTrace (prefixWord ++ tailWord_1113579) baseStart_1113579 baseEnd_1113579 := by
    simpa [prefixWord, tailWord_1113579, baseEnd_1113579] using wordTrace_append hprefix tailTrace_1113579
  have hstable : (prefixWord ++ tailWord_1113579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113579).length < 2 ^ (prefixWord ++ tailWord_1113579).sum := by decide
  have hdescent : baseEnd_1113579 < baseStart_1113579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113581 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1113581 : Nat := 118140960795 + 1113581 * 2 ^ 59
def prefixEnd_1113581 : Nat := 4983230072969 + 3 ^ 40 * 1113581 * 2
def baseEnd_1113581 : Nat := 571802300714512842916241

theorem tailTrace_1113581 : CollatzResearch.WordTrace tailWord_1113581 prefixEnd_1113581 571802300714512842916241 := by
  unfold tailWord_1113581
  simp only [CollatzResearch.WordTrace]
  refine ⟨40615635778693696338548597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27077090519129130892365731 40615635778693696338548597)
  ·
    refine ⟨3807715854252534031738931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40615635778693696338548597 3807715854252534031738931)
    ·
      refine ⟨5711573781378801047608397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3807715854252534031738931 5711573781378801047608397)
      ·
        refine ⟨2141840168017050392853149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5711573781378801047608397 2141840168017050392853149)
        ·
          refine ⟨803190063006393897319931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2141840168017050392853149 803190063006393897319931)
          ·
            refine ⟨1204785094509590845979897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803190063006393897319931 1204785094509590845979897)
            ·
              refine ⟨903588820882193134484923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204785094509590845979897 903588820882193134484923)
              ·
                refine ⟨1355383231323289701727385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903588820882193134484923 1355383231323289701727385)
                ·
                  refine ⟨1016537423492467276295539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1355383231323289701727385 1016537423492467276295539)
                  ·
                    refine ⟨1524806135238700914443309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1016537423492467276295539 1524806135238700914443309)
                    ·
                      refine ⟨571802300714512842916241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1524806135238700914443309 571802300714512842916241)
                      ·
                        rfl

theorem cell23_1113581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1113581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113581 prefixEnd_1113581 := by exact prefixLift 1113581
  have htrace : WordTrace (prefixWord ++ tailWord_1113581) baseStart_1113581 baseEnd_1113581 := by
    simpa [prefixWord, tailWord_1113581, baseEnd_1113581] using wordTrace_append hprefix tailTrace_1113581
  have hstable : (prefixWord ++ tailWord_1113581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113581).length < 2 ^ (prefixWord ++ tailWord_1113581).sum := by decide
  have hdescent : baseEnd_1113581 < baseStart_1113581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113626 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1113626 : Nat := 118140960795 + 1113626 * 2 ^ 59
def prefixEnd_1113626 : Nat := 4983230072969 + 3 ^ 40 * 1113626 * 2
def baseEnd_1113626 : Nat := 571825407343965166853533

theorem tailTrace_1113626 : CollatzResearch.WordTrace tailWord_1113626 prefixEnd_1113626 571825407343965166853533 := by
  unfold tailWord_1113626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10154319265882667255984183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27078184709020446015957821 10154319265882667255984183)
  ·
    refine ⟨15231478898824000883976275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10154319265882667255984183 15231478898824000883976275)
    ·
      refine ⟨22847218348236001325964413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15231478898824000883976275 22847218348236001325964413)
      ·
        refine ⟨8567706880588500497236655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22847218348236001325964413 8567706880588500497236655)
        ·
          refine ⟨12851560320882750745854983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8567706880588500497236655 12851560320882750745854983)
          ·
            refine ⟨19277340481324126118782475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12851560320882750745854983 19277340481324126118782475)
            ·
              refine ⟨28916010721986189178173713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19277340481324126118782475 28916010721986189178173713)
              ·
                refine ⟨21687008041489641883630285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28916010721986189178173713 21687008041489641883630285)
                ·
                  refine ⟨8132628015558615706361357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21687008041489641883630285 8132628015558615706361357)
                  ·
                    refine ⟨3049735505834480889885509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8132628015558615706361357 3049735505834480889885509)
                    ·
                      refine ⟨571825407343965166853533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3049735505834480889885509 571825407343965166853533)
                      ·
                        rfl

theorem cell23_1113626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1113626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113626 prefixEnd_1113626 := by exact prefixLift 1113626
  have htrace : WordTrace (prefixWord ++ tailWord_1113626) baseStart_1113626 baseEnd_1113626 := by
    simpa [prefixWord, tailWord_1113626, baseEnd_1113626] using wordTrace_append hprefix tailTrace_1113626
  have hstable : (prefixWord ++ tailWord_1113626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113626).length < 2 ^ (prefixWord ++ tailWord_1113626).sum := by decide
  have hdescent : baseEnd_1113626 < baseStart_1113626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113653 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1113653 : Nat := 118140960795 + 1113653 * 2 ^ 59
def prefixEnd_1113653 : Nat := 4983230072969 + 3 ^ 40 * 1113653 * 2
def baseEnd_1113653 : Nat := 190613090440545520405303

theorem tailTrace_1113653 : CollatzResearch.WordTrace tailWord_1113653 prefixEnd_1113653 190613090440545520405303 := by
  unfold tailWord_1113653
  simp only [CollatzResearch.WordTrace]
  refine ⟨40618261834432852635169613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27078841222955235090113075 40618261834432852635169613)
  ·
    refine ⟨15231848187912319738188605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40618261834432852635169613 15231848187912319738188605)
    ·
      refine ⟨5711943070467119901820727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15231848187912319738188605 5711943070467119901820727)
      ·
        refine ⟨8567914605700679852731091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5711943070467119901820727 8567914605700679852731091)
        ·
          refine ⟨12851871908551019779096637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8567914605700679852731091 12851871908551019779096637)
          ·
            refine ⟨4819451965706632417161239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12851871908551019779096637 4819451965706632417161239)
            ·
              refine ⟨7229177948559948625741859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819451965706632417161239 7229177948559948625741859)
              ·
                refine ⟨10843766922839922938612789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7229177948559948625741859 10843766922839922938612789)
                ·
                  refine ⟨1016603149016242775494949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10843766922839922938612789 1016603149016242775494949)
                  ·
                    refine ⟨190613090440545520405303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1016603149016242775494949 190613090440545520405303)
                    ·
                      rfl

theorem cell23_1113653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1113653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113653 prefixEnd_1113653 := by exact prefixLift 1113653
  have htrace : WordTrace (prefixWord ++ tailWord_1113653) baseStart_1113653 baseEnd_1113653 := by
    simpa [prefixWord, tailWord_1113653, baseEnd_1113653] using wordTrace_append hprefix tailTrace_1113653
  have hstable : (prefixWord ++ tailWord_1113653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113653).length < 2 ^ (prefixWord ++ tailWord_1113653).sum := by decide
  have hdescent : baseEnd_1113653 < baseStart_1113653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113663 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 3]
def baseStart_1113663 : Nat := 118140960795 + 1113663 * 2 ^ 59
def prefixEnd_1113663 : Nat := 4983230072969 + 3 ^ 40 * 1113663 * 2
def baseEnd_1113663 : Nat := 571844406128181522090863

theorem tailTrace_1113663 : CollatzResearch.WordTrace tailWord_1113663 prefixEnd_1113663 571844406128181522090863 := by
  unfold tailWord_1113663
  simp only [CollatzResearch.WordTrace]
  refine ⟨40618626564396624343033643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27079084376264416228689095 40618626564396624343033643)
  ·
    refine ⟨60927939846594936514550465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40618626564396624343033643 60927939846594936514550465)
    ·
      refine ⟨45695954884946202385912849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60927939846594936514550465 45695954884946202385912849)
      ·
        refine ⟨34271966163709651789434637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45695954884946202385912849 34271966163709651789434637)
        ·
          refine ⟨12851987311391119421037989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34271966163709651789434637 12851987311391119421037989)
          ·
            refine ⟨2409747620885834891444623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12851987311391119421037989 2409747620885834891444623)
            ·
              refine ⟨3614621431328752337166935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2409747620885834891444623 3614621431328752337166935)
              ·
                refine ⟨5421932146993128505750403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3614621431328752337166935 5421932146993128505750403)
                ·
                  refine ⟨8132898220489692758625605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5421932146993128505750403 8132898220489692758625605)
                  ·
                    refine ⟨1524918416341817392242301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8132898220489692758625605 1524918416341817392242301)
                    ·
                      refine ⟨571844406128181522090863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1524918416341817392242301 571844406128181522090863)
                      ·
                        rfl

theorem cell23_1113663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_1113663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113663 prefixEnd_1113663 := by exact prefixLift 1113663
  have htrace : WordTrace (prefixWord ++ tailWord_1113663) baseStart_1113663 baseEnd_1113663 := by
    simpa [prefixWord, tailWord_1113663, baseEnd_1113663] using wordTrace_append hprefix tailTrace_1113663
  have hstable : (prefixWord ++ tailWord_1113663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113663).length < 2 ^ (prefixWord ++ tailWord_1113663).sum := by decide
  have hdescent : baseEnd_1113663 < baseStart_1113663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113700 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 6]
def baseStart_1113700 : Nat := 118140960795 + 1113700 * 2 ^ 59
def prefixEnd_1113700 : Nat := 4983230072969 + 3 ^ 40 * 1113700 * 2
def baseEnd_1113700 : Nat := 63540378323599764147577

theorem tailTrace_1113700 : CollatzResearch.WordTrace tailWord_1113700 prefixEnd_1113700 63540378323599764147577 := by
  unfold tailWord_1113700
  simp only [CollatzResearch.WordTrace]
  refine ⟨20309988032631289831065277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27079984043508386441420369 20309988032631289831065277)
  ·
    refine ⟨7616245512236733686649479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20309988032631289831065277 7616245512236733686649479)
    ·
      refine ⟨11424368268355100529974219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7616245512236733686649479 11424368268355100529974219)
      ·
        refine ⟨17136552402532650794961329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11424368268355100529974219 17136552402532650794961329)
        ·
          refine ⟨12852414301899488096220997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17136552402532650794961329 12852414301899488096220997)
          ·
            refine ⟨2409827681606154018041437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12852414301899488096220997 2409827681606154018041437)
            ·
              refine ⟨903685380602307756765539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2409827681606154018041437 903685380602307756765539)
              ·
                refine ⟨1355528070903461635148309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903685380602307756765539 1355528070903461635148309)
                ·
                  refine ⟨63540378323599764147577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1355528070903461635148309 63540378323599764147577)
                  ·
                    rfl

theorem cell23_1113700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_1113700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113700 prefixEnd_1113700 := by exact prefixLift 1113700
  have htrace : WordTrace (prefixWord ++ tailWord_1113700) baseStart_1113700 baseEnd_1113700 := by
    simpa [prefixWord, tailWord_1113700, baseEnd_1113700] using wordTrace_append hprefix tailTrace_1113700
  have hstable : (prefixWord ++ tailWord_1113700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113700).length < 2 ^ (prefixWord ++ tailWord_1113700).sum := by decide
  have hdescent : baseEnd_1113700 < baseStart_1113700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113763 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 4]
def baseStart_1113763 : Nat := 118140960795 + 1113763 * 2 ^ 59
def prefixEnd_1113763 : Nat := 4983230072969 + 3 ^ 40 * 1113763 * 2
def baseEnd_1113763 : Nat := 571895754193631130840403

theorem tailTrace_1113763 : CollatzResearch.WordTrace tailWord_1113763 prefixEnd_1113763 571895754193631130840403 := by
  unfold tailWord_1113763
  simp only [CollatzResearch.WordTrace]
  refine ⟨40622273864034341421673943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27081515909356227614449295 40622273864034341421673943)
  ·
    refine ⟨60933410796051512132510915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40622273864034341421673943 60933410796051512132510915)
    ·
      refine ⟨91400116194077268198766373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60933410796051512132510915 91400116194077268198766373)
      ·
        refine ⟨17137521786389487787268695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91400116194077268198766373 17137521786389487787268695)
        ·
          refine ⟨25706282679584231680903043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17137521786389487787268695 25706282679584231680903043)
          ·
            refine ⟨38559424019376347521354565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25706282679584231680903043 38559424019376347521354565)
            ·
              refine ⟨7229892003633065160253981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38559424019376347521354565 7229892003633065160253981)
              ·
                refine ⟨2711209501362399435095243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7229892003633065160253981 2711209501362399435095243)
                ·
                  refine ⟨4066814252043599152642865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2711209501362399435095243 4066814252043599152642865)
                  ·
                    refine ⟨3050110689032699364482149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4066814252043599152642865 3050110689032699364482149)
                    ·
                      refine ⟨571895754193631130840403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3050110689032699364482149 571895754193631130840403)
                      ·
                        rfl

theorem cell23_1113763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_1113763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113763 prefixEnd_1113763 := by exact prefixLift 1113763
  have htrace : WordTrace (prefixWord ++ tailWord_1113763) baseStart_1113763 baseEnd_1113763 := by
    simpa [prefixWord, tailWord_1113763, baseEnd_1113763] using wordTrace_append hprefix tailTrace_1113763
  have hstable : (prefixWord ++ tailWord_1113763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113763).length < 2 ^ (prefixWord ++ tailWord_1113763).sum := by decide
  have hdescent : baseEnd_1113763 < baseStart_1113763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113773 : List Nat := [1, 5, 2, 1, 1, 1, 1, 11]
def baseStart_1113773 : Nat := 118140960795 + 1113773 * 2 ^ 59
def prefixEnd_1113773 : Nat := 4983230072969 + 3 ^ 40 * 1113773 * 2
def baseEnd_1113773 : Nat := 21181514407413929322791

theorem tailTrace_1113773 : CollatzResearch.WordTrace tailWord_1113773 prefixEnd_1113773 21181514407413929322791 := by
  unfold tailWord_1113773
  simp only [CollatzResearch.WordTrace]
  refine ⟨40622638593998113129537973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27081759062665408753025315 40622638593998113129537973)
  ·
    refine ⟨3808372368187323105894185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40622638593998113129537973 3808372368187323105894185)
    ·
      refine ⟨2856279276140492329420639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3808372368187323105894185 2856279276140492329420639)
      ·
        refine ⟨4284418914210738494130959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2856279276140492329420639 4284418914210738494130959)
        ·
          refine ⟨6426628371316107741196439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4284418914210738494130959 6426628371316107741196439)
          ·
            refine ⟨9639942556974161611794659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6426628371316107741196439 9639942556974161611794659)
            ·
              refine ⟨14459913835461242417691989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9639942556974161611794659 14459913835461242417691989)
              ·
                refine ⟨21181514407413929322791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 14459913835461242417691989 21181514407413929322791)
                ·
                  rfl

theorem cell23_1113773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 11].length) (baseStart_1113773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113773 prefixEnd_1113773 := by exact prefixLift 1113773
  have htrace : WordTrace (prefixWord ++ tailWord_1113773) baseStart_1113773 baseEnd_1113773 := by
    simpa [prefixWord, tailWord_1113773, baseEnd_1113773] using wordTrace_append hprefix tailTrace_1113773
  have hstable : (prefixWord ++ tailWord_1113773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113773).length < 2 ^ (prefixWord ++ tailWord_1113773).sum := by decide
  have hdescent : baseEnd_1113773 < baseStart_1113773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113817 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 3]
def baseStart_1113817 : Nat := 118140960795 + 1113817 * 2 ^ 59
def prefixEnd_1113817 : Nat := 4983230072969 + 3 ^ 40 * 1113817 * 2
def baseEnd_1113817 : Nat := 571923482148973919565155

theorem tailTrace_1113817 : CollatzResearch.WordTrace tailWord_1113817 prefixEnd_1113817 571923482148973919565155 := by
  unfold tailWord_1113817
  simp only [CollatzResearch.WordTrace]
  refine ⟨40624243405838708644139705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27082828937225805762759803 40624243405838708644139705)
  ·
    refine ⟨30468182554379031483104779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40624243405838708644139705 30468182554379031483104779)
    ·
      refine ⟨45702273831568547224657169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30468182554379031483104779 45702273831568547224657169)
      ·
        refine ⟨34276705373676410418492877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45702273831568547224657169 34276705373676410418492877)
        ·
          refine ⟨12853764515128653906934829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34276705373676410418492877 12853764515128653906934829)
          ·
            refine ⟨4820161693173245215100561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12853764515128653906934829 4820161693173245215100561)
            ·
              refine ⟨3615121269879933911325421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4820161693173245215100561 3615121269879933911325421)
              ·
                refine ⟨1355670476204975216747033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3615121269879933911325421 1355670476204975216747033)
                ·
                  refine ⟨1016752857153731412560275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1355670476204975216747033 1016752857153731412560275)
                  ·
                    refine ⟨1525129285730597118840413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1016752857153731412560275 1525129285730597118840413)
                    ·
                      refine ⟨571923482148973919565155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1525129285730597118840413 571923482148973919565155)
                      ·
                        rfl

theorem cell23_1113817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_1113817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113817 prefixEnd_1113817 := by exact prefixLift 1113817
  have htrace : WordTrace (prefixWord ++ tailWord_1113817) baseStart_1113817 baseEnd_1113817 := by
    simpa [prefixWord, tailWord_1113817, baseEnd_1113817] using wordTrace_append hprefix tailTrace_1113817
  have hstable : (prefixWord ++ tailWord_1113817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113817).length < 2 ^ (prefixWord ++ tailWord_1113817).sum := by decide
  have hdescent : baseEnd_1113817 < baseStart_1113817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113823 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1113823 : Nat := 118140960795 + 1113823 * 2 ^ 59
def prefixEnd_1113823 : Nat := 4983230072969 + 3 ^ 40 * 1113823 * 2
def baseEnd_1113823 : Nat := 571926563032900896090127

theorem tailTrace_1113823 : CollatzResearch.WordTrace tailWord_1113823 prefixEnd_1113823 571926563032900896090127 := by
  unfold tailWord_1113823
  simp only [CollatzResearch.WordTrace]
  refine ⟨40624462243816971668858123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27082974829211314445905415 40624462243816971668858123)
  ·
    refine ⟨60936693365725457503287185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40624462243816971668858123 60936693365725457503287185)
    ·
      refine ⟨45702520024294093127465389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60936693365725457503287185 45702520024294093127465389)
      ·
        refine ⟨17138445009110284922799521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45702520024294093127465389 17138445009110284922799521)
        ·
          refine ⟨12853833756832713692099641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17138445009110284922799521 12853833756832713692099641)
          ·
            refine ⟨9640375317624535269074731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12853833756832713692099641 9640375317624535269074731)
            ·
              refine ⟨14460562976436802903612097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9640375317624535269074731 14460562976436802903612097)
              ·
                refine ⟨10845422232327602177709073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14460562976436802903612097 10845422232327602177709073)
                ·
                  refine ⟨8134066674245701633281805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10845422232327602177709073 8134066674245701633281805)
                  ·
                    refine ⟨3050275002842138112480677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8134066674245701633281805 3050275002842138112480677)
                    ·
                      refine ⟨571926563032900896090127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3050275002842138112480677 571926563032900896090127)
                      ·
                        rfl

theorem cell23_1113823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1113823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113823 prefixEnd_1113823 := by exact prefixLift 1113823
  have htrace : WordTrace (prefixWord ++ tailWord_1113823) baseStart_1113823 baseEnd_1113823 := by
    simpa [prefixWord, tailWord_1113823, baseEnd_1113823] using wordTrace_append hprefix tailTrace_1113823
  have hstable : (prefixWord ++ tailWord_1113823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113823).length < 2 ^ (prefixWord ++ tailWord_1113823).sum := by decide
  have hdescent : baseEnd_1113823 < baseStart_1113823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113840 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 3, 4, 2]
def baseStart_1113840 : Nat := 118140960795 + 1113840 * 2 ^ 59
def prefixEnd_1113840 : Nat := 4983230072969 + 3 ^ 40 * 1113840 * 2
def baseEnd_1113840 : Nat := 571935292204027329577549

theorem tailTrace_1113840 : CollatzResearch.WordTrace tailWord_1113840 prefixEnd_1113840 571935292204027329577549 := by
  unfold tailWord_1113840
  simp only [CollatzResearch.WordTrace]
  refine ⟨20312541142377691786113487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27083388189836922381484649 20312541142377691786113487)
  ·
    refine ⟨30468811713566537679170231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20312541142377691786113487 30468811713566537679170231)
    ·
      refine ⟨45703217570349806518755347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30468811713566537679170231 45703217570349806518755347)
      ·
        refine ⟨68554826355524709778133021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45703217570349806518755347 68554826355524709778133021)
        ·
          refine ⟨25708059883321766166799883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68554826355524709778133021 25708059883321766166799883)
          ·
            refine ⟨38562089824982649250199825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25708059883321766166799883 38562089824982649250199825)
            ·
              refine ⟨28921567368736986937649869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38562089824982649250199825 28921567368736986937649869)
              ·
                refine ⟨10845587763276370101618701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28921567368736986937649869 10845587763276370101618701)
                ·
                  refine ⟨4067095411228638788107013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10845587763276370101618701 4067095411228638788107013)
                  ·
                    refine ⟨762580389605369772770065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4067095411228638788107013 762580389605369772770065)
                    ·
                      refine ⟨571935292204027329577549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762580389605369772770065 571935292204027329577549)
                      ·
                        rfl

theorem cell23_1113840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 4, 2].length) (baseStart_1113840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113840 prefixEnd_1113840 := by exact prefixLift 1113840
  have htrace : WordTrace (prefixWord ++ tailWord_1113840) baseStart_1113840 baseEnd_1113840 := by
    simpa [prefixWord, tailWord_1113840, baseEnd_1113840] using wordTrace_append hprefix tailTrace_1113840
  have hstable : (prefixWord ++ tailWord_1113840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113840).length < 2 ^ (prefixWord ++ tailWord_1113840).sum := by decide
  have hdescent : baseEnd_1113840 < baseStart_1113840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113843 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 5]
def baseStart_1113843 : Nat := 118140960795 + 1113843 * 2 ^ 59
def prefixEnd_1113843 : Nat := 4983230072969 + 3 ^ 40 * 1113843 * 2
def baseEnd_1113843 : Nat := 571936832645990817840035

theorem tailTrace_1113843 : CollatzResearch.WordTrace tailWord_1113843 prefixEnd_1113843 571936832645990817840035 := by
  unfold tailWord_1113843
  simp only [CollatzResearch.WordTrace]
  refine ⟨40625191703744515084586183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27083461135829676723057455 40625191703744515084586183)
  ·
    refine ⟨60937787555616772626879275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40625191703744515084586183 60937787555616772626879275)
    ·
      refine ⟨91406681333425158940318913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60937787555616772626879275 91406681333425158940318913)
      ·
        refine ⟨68555011000068869205239185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91406681333425158940318913 68555011000068869205239185)
        ·
          refine ⟨51416258250051651903929389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68555011000068869205239185 51416258250051651903929389)
          ·
            refine ⟨19281096843769369463973521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51416258250051651903929389 19281096843769369463973521)
            ·
              refine ⟨14460822632827027097980141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19281096843769369463973521 14460822632827027097980141)
              ·
                refine ⟨5422808487310135161742553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14460822632827027097980141 5422808487310135161742553)
                ·
                  refine ⟨4067106365482601371306915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5422808487310135161742553 4067106365482601371306915)
                  ·
                    refine ⟨6100659548223902056960373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4067106365482601371306915 6100659548223902056960373)
                    ·
                      refine ⟨571936832645990817840035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6100659548223902056960373 571936832645990817840035)
                      ·
                        rfl

theorem cell23_1113843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_1113843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113843 prefixEnd_1113843 := by exact prefixLift 1113843
  have htrace : WordTrace (prefixWord ++ tailWord_1113843) baseStart_1113843 baseEnd_1113843 := by
    simpa [prefixWord, tailWord_1113843, baseEnd_1113843] using wordTrace_append hprefix tailTrace_1113843
  have hstable : (prefixWord ++ tailWord_1113843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113843).length < 2 ^ (prefixWord ++ tailWord_1113843).sum := by decide
  have hdescent : baseEnd_1113843 < baseStart_1113843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113862 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1113862 : Nat := 118140960795 + 1113862 * 2 ^ 59
def prefixEnd_1113862 : Nat := 4983230072969 + 3 ^ 40 * 1113862 * 2
def baseEnd_1113862 : Nat := 190648862926142081167483

theorem tailTrace_1113862 : CollatzResearch.WordTrace tailWord_1113862 prefixEnd_1113862 190648862926142081167483 := by
  unfold tailWord_1113862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269558896583615041547745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27083923127117120886351893 1269558896583615041547745)
  ·
    refine ⟨952169172437711281160809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1269558896583615041547745 952169172437711281160809)
    ·
      refine ⟨714126879328283460870607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 952169172437711281160809 714126879328283460870607)
      ·
        refine ⟨1071190318992425191305911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714126879328283460870607 1071190318992425191305911)
        ·
          refine ⟨1606785478488637786958867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071190318992425191305911 1606785478488637786958867)
          ·
            refine ⟨2410178217732956680438301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606785478488637786958867 2410178217732956680438301)
            ·
              refine ⟨903816831649858755164363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2410178217732956680438301 903816831649858755164363)
              ·
                refine ⟨1355725247474788132746545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903816831649858755164363 1355725247474788132746545)
                ·
                  refine ⟨1016793935606091099559909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1355725247474788132746545 1016793935606091099559909)
                  ·
                    refine ⟨190648862926142081167483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1016793935606091099559909 190648862926142081167483)
                    ·
                      rfl

theorem cell23_1113862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1113862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113862 prefixEnd_1113862 := by exact prefixLift 1113862
  have htrace : WordTrace (prefixWord ++ tailWord_1113862) baseStart_1113862 baseEnd_1113862 := by
    simpa [prefixWord, tailWord_1113862, baseEnd_1113862] using wordTrace_append hprefix tailTrace_1113862
  have hstable : (prefixWord ++ tailWord_1113862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113862).length < 2 ^ (prefixWord ++ tailWord_1113862).sum := by decide
  have hdescent : baseEnd_1113862 < baseStart_1113862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113870 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1113870 : Nat := 118140960795 + 1113870 * 2 ^ 59
def prefixEnd_1113870 : Nat := 4983230072969 + 3 ^ 40 * 1113870 * 2
def baseEnd_1113870 : Nat := 571950696623662212202411

theorem tailTrace_1113870 : CollatzResearch.WordTrace tailWord_1113870 prefixEnd_1113870 571950696623662212202411 := by
  unfold tailWord_1113870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5078272059330837336977383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27084117649764465797212709 5078272059330837336977383)
  ·
    refine ⟨7617408088996256005466075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5078272059330837336977383 7617408088996256005466075)
    ·
      refine ⟨11426112133494384008199113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7617408088996256005466075 11426112133494384008199113)
      ·
        refine ⟨8569584100120788006149335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11426112133494384008199113 8569584100120788006149335)
        ·
          refine ⟨12854376150181182009224003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8569584100120788006149335 12854376150181182009224003)
          ·
            refine ⟨19281564225271773013836005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12854376150181182009224003 19281564225271773013836005)
            ·
              refine ⟨3615293292238457440094251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19281564225271773013836005 3615293292238457440094251)
              ·
                refine ⟨5422939938357686160141377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615293292238457440094251 5422939938357686160141377)
                ·
                  refine ⟨4067204953768264620106033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5422939938357686160141377 4067204953768264620106033)
                  ·
                    refine ⟨3050403715326198465079525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4067204953768264620106033 3050403715326198465079525)
                    ·
                      refine ⟨571950696623662212202411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3050403715326198465079525 571950696623662212202411)
                      ·
                        rfl

theorem cell23_1113870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1113870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113870 prefixEnd_1113870 := by exact prefixLift 1113870
  have htrace : WordTrace (prefixWord ++ tailWord_1113870) baseStart_1113870 baseEnd_1113870 := by
    simpa [prefixWord, tailWord_1113870, baseEnd_1113870] using wordTrace_append hprefix tailTrace_1113870
  have hstable : (prefixWord ++ tailWord_1113870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113870).length < 2 ^ (prefixWord ++ tailWord_1113870).sum := by decide
  have hdescent : baseEnd_1113870 < baseStart_1113870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113903 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_1113903 : Nat := 118140960795 + 1113903 * 2 ^ 59
def prefixEnd_1113903 : Nat := 4983230072969 + 3 ^ 40 * 1113903 * 2
def baseEnd_1113903 : Nat := 571967641485260583089759

theorem tailTrace_1113903 : CollatzResearch.WordTrace tailWord_1113903 prefixEnd_1113903 571967641485260583089759 := by
  unfold tailWord_1113903
  simp only [CollatzResearch.WordTrace]
  refine ⟨40627380083527145331770363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27084920055684763554513575 40627380083527145331770363)
  ·
    refine ⟨60941070125290717997655545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40627380083527145331770363 60941070125290717997655545)
    ·
      refine ⟨45705802593968038498241659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60941070125290717997655545 45705802593968038498241659)
      ·
        refine ⟨68558703890952057747362489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45705802593968038498241659 68558703890952057747362489)
        ·
          refine ⟨51419027918214043310521867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68558703890952057747362489 51419027918214043310521867)
          ·
            refine ⟨77128541877321064965782801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51419027918214043310521867 77128541877321064965782801)
            ·
              refine ⟨57846406407990798724337101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77128541877321064965782801 57846406407990798724337101)
              ·
                refine ⟨21692402402996549521626413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57846406407990798724337101 21692402402996549521626413)
                ·
                  refine ⟨8134650901123706070609905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21692402402996549521626413 8134650901123706070609905)
                  ·
                    refine ⟨6100988175842779552957429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8134650901123706070609905 6100988175842779552957429)
                    ·
                      refine ⟨571967641485260583089759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6100988175842779552957429 571967641485260583089759)
                      ·
                        rfl

theorem cell23_1113903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_1113903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113903 prefixEnd_1113903 := by exact prefixLift 1113903
  have htrace : WordTrace (prefixWord ++ tailWord_1113903) baseStart_1113903 baseEnd_1113903 := by
    simpa [prefixWord, tailWord_1113903, baseEnd_1113903] using wordTrace_append hprefix tailTrace_1113903
  have hstable : (prefixWord ++ tailWord_1113903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113903).length < 2 ^ (prefixWord ++ tailWord_1113903).sum := by decide
  have hdescent : baseEnd_1113903 < baseStart_1113903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113914 : List Nat := [3, 1, 1, 1, 5, 2, 3, 2, 5]
def baseStart_1113914 : Nat := 118140960795 + 1113914 * 2 ^ 59
def prefixEnd_1113914 : Nat := 4983230072969 + 3 ^ 40 * 1113914 * 2
def baseEnd_1113914 : Nat := 63552587752495560005801

theorem tailTrace_1113914 : CollatzResearch.WordTrace tailWord_1113914 prefixEnd_1113914 63552587752495560005801 := by
  unfold tailWord_1113914
  simp only [CollatzResearch.WordTrace]
  refine ⟨10156945321621823552605199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27085187524324862806947197 10156945321621823552605199)
  ·
    refine ⟨15235417982432735328907799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10156945321621823552605199 15235417982432735328907799)
    ·
      refine ⟨22853126973649102993361699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15235417982432735328907799 22853126973649102993361699)
      ·
        refine ⟨34279690460473654490042549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22853126973649102993361699 34279690460473654490042549)
        ·
          refine ⟨3213720980669405108441489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34279690460473654490042549 3213720980669405108441489)
          ·
            refine ⟨2410290735502053831331117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3213720980669405108441489 2410290735502053831331117)
            ·
              refine ⟨903859025813270186749169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2410290735502053831331117 903859025813270186749169)
              ·
                refine ⟨677894269359952640061877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903859025813270186749169 677894269359952640061877)
                ·
                  refine ⟨63552587752495560005801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 677894269359952640061877 63552587752495560005801)
                  ·
                    rfl

theorem cell23_1113914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_1113914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113914 prefixEnd_1113914 := by exact prefixLift 1113914
  have htrace : WordTrace (prefixWord ++ tailWord_1113914) baseStart_1113914 baseEnd_1113914 := by
    simpa [prefixWord, tailWord_1113914, baseEnd_1113914] using wordTrace_append hprefix tailTrace_1113914
  have hstable : (prefixWord ++ tailWord_1113914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113914).length < 2 ^ (prefixWord ++ tailWord_1113914).sum := by decide
  have hdescent : baseEnd_1113914 < baseStart_1113914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113930 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1113930 : Nat := 118140960795 + 1113930 * 2 ^ 59
def prefixEnd_1113930 : Nat := 4983230072969 + 3 ^ 40 * 1113930 * 2
def baseEnd_1113930 : Nat := 571981505462931977452135

theorem tailTrace_1113930 : CollatzResearch.WordTrace tailWord_1113930 prefixEnd_1113930 571981505462931977452135 := by
  unfold tailWord_1113930
  simp only [CollatzResearch.WordTrace]
  refine ⟨10157091213607332235750811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27085576569619552628668829 10157091213607332235750811)
  ·
    refine ⟨15235636820410998353626217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10157091213607332235750811 15235636820410998353626217)
    ·
      refine ⟨11426727615308248765219663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15235636820410998353626217 11426727615308248765219663)
      ·
        refine ⟨17140091422962373147829495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11426727615308248765219663 17140091422962373147829495)
        ·
          refine ⟨25710137134443559721744243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17140091422962373147829495 25710137134443559721744243)
          ·
            refine ⟨38565205701665339582616365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25710137134443559721744243 38565205701665339582616365)
            ·
              refine ⟨14461952138124502343481137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38565205701665339582616365 14461952138124502343481137)
              ·
                refine ⟨10846464103593376757610853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14461952138124502343481137 10846464103593376757610853)
                ·
                  refine ⟨2033712019423758142052035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10846464103593376757610853 2033712019423758142052035)
                  ·
                    refine ⟨3050568029135637213078053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2033712019423758142052035 3050568029135637213078053)
                    ·
                      refine ⟨571981505462931977452135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3050568029135637213078053 571981505462931977452135)
                      ·
                        rfl

theorem cell23_1113930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1113930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113930 prefixEnd_1113930 := by exact prefixLift 1113930
  have htrace : WordTrace (prefixWord ++ tailWord_1113930) baseStart_1113930 baseEnd_1113930 := by
    simpa [prefixWord, tailWord_1113930, baseEnd_1113930] using wordTrace_append hprefix tailTrace_1113930
  have hstable : (prefixWord ++ tailWord_1113930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113930).length < 2 ^ (prefixWord ++ tailWord_1113930).sum := by decide
  have hdescent : baseEnd_1113930 < baseStart_1113930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113960 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1113960 : Nat := 118140960795 + 1113960 * 2 ^ 59
def prefixEnd_1113960 : Nat := 4983230072969 + 3 ^ 40 * 1113960 * 2
def baseEnd_1113960 : Nat := 571996909882566860076997

theorem tailTrace_1113960 : CollatzResearch.WordTrace tailWord_1113960 prefixEnd_1113960 571996909882566860076997 := by
  unfold tailWord_1113960
  simp only [CollatzResearch.WordTrace]
  refine ⟨20314729522160322033297667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27086306029547096044396889 20314729522160322033297667)
  ·
    refine ⟨30472094283240483049946501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20314729522160322033297667 30472094283240483049946501)
    ·
      refine ⟨5713517678107590571864969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30472094283240483049946501 5713517678107590571864969)
      ·
        refine ⟨4285138258580692928898727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5713517678107590571864969 4285138258580692928898727)
        ·
          refine ⟨6427707387871039393348091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285138258580692928898727 6427707387871039393348091)
          ·
            refine ⟨9641561081806559090022137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6427707387871039393348091 9641561081806559090022137)
            ·
              refine ⟨7231170811354919317516603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9641561081806559090022137 7231170811354919317516603)
              ·
                refine ⟨10846756217032378976274905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7231170811354919317516603 10846756217032378976274905)
                ·
                  refine ⟨8135067162774284232206179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10846756217032378976274905 8135067162774284232206179)
                  ·
                    refine ⟨12202600744161426348309269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8135067162774284232206179 12202600744161426348309269)
                    ·
                      refine ⟨571996909882566860076997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12202600744161426348309269 571996909882566860076997)
                      ·
                        rfl

theorem cell23_1113960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1113960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113960 prefixEnd_1113960 := by exact prefixLift 1113960
  have htrace : WordTrace (prefixWord ++ tailWord_1113960) baseStart_1113960 baseEnd_1113960 := by
    simpa [prefixWord, tailWord_1113960, baseEnd_1113960] using wordTrace_append hprefix tailTrace_1113960
  have hstable : (prefixWord ++ tailWord_1113960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113960).length < 2 ^ (prefixWord ++ tailWord_1113960).sum := by decide
  have hdescent : baseEnd_1113960 < baseStart_1113960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113980 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_1113980 : Nat := 118140960795 + 1113980 * 2 ^ 59
def prefixEnd_1113980 : Nat := 4983230072969 + 3 ^ 40 * 1113980 * 2
def baseEnd_1113980 : Nat := 572007179495656781826905

theorem tailTrace_1113980 : CollatzResearch.WordTrace tailWord_1113980 prefixEnd_1113980 572007179495656781826905 := by
  unfold tailWord_1113980
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315094252124093741161697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27086792336165458321548929 20315094252124093741161697)
  ·
    refine ⟨15236320689093070305871273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20315094252124093741161697 15236320689093070305871273)
    ·
      refine ⟨11427240516819802729403455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15236320689093070305871273 11427240516819802729403455)
      ·
        refine ⟨17140860775229704094105183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11427240516819802729403455 17140860775229704094105183)
        ·
          refine ⟨25711291162844556141157775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17140860775229704094105183 25711291162844556141157775)
          ·
            refine ⟨38566936744266834211736663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25711291162844556141157775 38566936744266834211736663)
            ·
              refine ⟨57850405116400251317604995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38566936744266834211736663 57850405116400251317604995)
              ·
                refine ⟨86775607674600376976407493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57850405116400251317604995 86775607674600376976407493)
                ·
                  refine ⟨16270426438987570683076405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86775607674600376976407493 16270426438987570683076405)
                  ·
                    refine ⟨1525352478655084751538413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16270426438987570683076405 1525352478655084751538413)
                    ·
                      refine ⟨572007179495656781826905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1525352478655084751538413 572007179495656781826905)
                      ·
                        rfl

theorem cell23_1113980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_1113980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113980 prefixEnd_1113980 := by exact prefixLift 1113980
  have htrace : WordTrace (prefixWord ++ tailWord_1113980) baseStart_1113980 baseEnd_1113980 := by
    simpa [prefixWord, tailWord_1113980, baseEnd_1113980] using wordTrace_append hprefix tailTrace_1113980
  have hstable : (prefixWord ++ tailWord_1113980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113980).length < 2 ^ (prefixWord ++ tailWord_1113980).sum := by decide
  have hdescent : baseEnd_1113980 < baseStart_1113980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113998 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1113998 : Nat := 118140960795 + 1113998 * 2 ^ 59
def prefixEnd_1113998 : Nat := 4983230072969 + 3 ^ 40 * 1113998 * 2
def baseEnd_1113998 : Nat := 572016422147437711401823

theorem tailTrace_1113998 : CollatzResearch.WordTrace tailWord_1113998 prefixEnd_1113998 572016422147437711401823 := by
  unfold tailWord_1113998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5078855627272872069559831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27087230012121984370985765 5078855627272872069559831)
  ·
    refine ⟨7618283440909308104339747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5078855627272872069559831 7618283440909308104339747)
    ·
      refine ⟨11427425161363962156509621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7618283440909308104339747 11427425161363962156509621)
      ·
        refine ⟨1071321108877871452172777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11427425161363962156509621 1071321108877871452172777)
        ·
          refine ⟨803490831658403589129583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1071321108877871452172777 803490831658403589129583)
          ·
            refine ⟨1205236247487605383694375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803490831658403589129583 1205236247487605383694375)
            ·
              refine ⟨1807854371231408075541563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205236247487605383694375 1807854371231408075541563)
              ·
                refine ⟨2711781556847112113312345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807854371231408075541563 2711781556847112113312345)
                ·
                  refine ⟨2033836167635334084984259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2711781556847112113312345 2033836167635334084984259)
                  ·
                    refine ⟨3050754251453001127476389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2033836167635334084984259 3050754251453001127476389)
                    ·
                      refine ⟨572016422147437711401823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3050754251453001127476389 572016422147437711401823)
                      ·
                        rfl

theorem cell23_1113998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1113998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1113998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1113998 prefixEnd_1113998 := by exact prefixLift 1113998
  have htrace : WordTrace (prefixWord ++ tailWord_1113998) baseStart_1113998 baseEnd_1113998 := by
    simpa [prefixWord, tailWord_1113998, baseEnd_1113998] using wordTrace_append hprefix tailTrace_1113998
  have hstable : (prefixWord ++ tailWord_1113998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113998).length < 2 ^ (prefixWord ++ tailWord_1113998).sum := by decide
  have hdescent : baseEnd_1113998 < baseStart_1113998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114008 : List Nat := [2, 1, 2, 6, 1, 1, 2, 3, 1, 4]
def baseStart_1114008 : Nat := 118140960795 + 1114008 * 2 ^ 59
def prefixEnd_1114008 : Nat := 4983230072969 + 3 ^ 40 * 1114008 * 2
def baseEnd_1114008 : Nat := 190673852317994224092259

theorem tailTrace_1114008 : CollatzResearch.WordTrace tailWord_1114008 prefixEnd_1114008 190673852317994224092259 := by
  unfold tailWord_1114008
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315604874073374132171339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27087473165431165509561785 20315604874073374132171339)
  ·
    refine ⟨30473407311110061198257009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20315604874073374132171339 30473407311110061198257009)
    ·
      refine ⟨22855055483332545898692757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30473407311110061198257009 22855055483332545898692757)
      ·
        refine ⟨1071330725781213089001223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22855055483332545898692757 1071330725781213089001223)
        ·
          refine ⟨1606996088671819633501835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071330725781213089001223 1606996088671819633501835)
          ·
            refine ⟨2410494133007729450252753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606996088671819633501835 2410494133007729450252753)
            ·
              refine ⟨1807870599755797087689565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2410494133007729450252753 1807870599755797087689565)
              ·
                refine ⟨677951474908423907883587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1807870599755797087689565 677951474908423907883587)
                ·
                  refine ⟨1016927212362635861825381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677951474908423907883587 1016927212362635861825381)
                  ·
                    refine ⟨190673852317994224092259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1016927212362635861825381 190673852317994224092259)
                    ·
                      rfl

theorem cell23_1114008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_1114008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114008 prefixEnd_1114008 := by exact prefixLift 1114008
  have htrace : WordTrace (prefixWord ++ tailWord_1114008) baseStart_1114008 baseEnd_1114008 := by
    simpa [prefixWord, tailWord_1114008, baseEnd_1114008] using wordTrace_append hprefix tailTrace_1114008
  have hstable : (prefixWord ++ tailWord_1114008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114008).length < 2 ^ (prefixWord ++ tailWord_1114008).sum := by decide
  have hdescent : baseEnd_1114008 < baseStart_1114008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114074 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_1114074 : Nat := 118140960795 + 1114074 * 2 ^ 59
def prefixEnd_1114074 : Nat := 4983230072969 + 3 ^ 40 * 1114074 * 2
def baseEnd_1114074 : Nat := 572055446677179414051473

theorem tailTrace_1114074 : CollatzResearch.WordTrace tailWord_1114074 prefixEnd_1114074 572055446677179414051473 := by
  unfold tailWord_1114074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158404241476910384061319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27089077977271761024163517 10158404241476910384061319)
  ·
    refine ⟨15237606362215365576091979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10158404241476910384061319 15237606362215365576091979)
    ·
      refine ⟨22856409543323048364137969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15237606362215365576091979 22856409543323048364137969)
      ·
        refine ⟨17142307157492286273103477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22856409543323048364137969 17142307157492286273103477)
        ·
          refine ⟨1607091296014901838103451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17142307157492286273103477 1607091296014901838103451)
          ·
            refine ⟨2410636944022352757155177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607091296014901838103451 2410636944022352757155177)
            ·
              refine ⟨1807977708016764567866383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2410636944022352757155177 1807977708016764567866383)
              ·
                refine ⟨2711966562025146851799575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807977708016764567866383 2711966562025146851799575)
                ·
                  refine ⟨4067949843037720277699363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2711966562025146851799575 4067949843037720277699363)
                  ·
                    refine ⟨6101924764556580416549045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4067949843037720277699363 6101924764556580416549045)
                    ·
                      refine ⟨572055446677179414051473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6101924764556580416549045 572055446677179414051473)
                      ·
                        rfl

theorem cell23_1114074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_1114074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114074 prefixEnd_1114074 := by exact prefixLift 1114074
  have htrace : WordTrace (prefixWord ++ tailWord_1114074) baseStart_1114074 baseEnd_1114074 := by
    simpa [prefixWord, tailWord_1114074, baseEnd_1114074] using wordTrace_append hprefix tailTrace_1114074
  have hstable : (prefixWord ++ tailWord_1114074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114074).length < 2 ^ (prefixWord ++ tailWord_1114074).sum := by decide
  have hdescent : baseEnd_1114074 < baseStart_1114074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114082 : List Nat := [3, 3, 3, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1114082 : Nat := 118140960795 + 1114082 * 2 ^ 59
def prefixEnd_1114082 : Nat := 4983230072969 + 3 ^ 40 * 1114082 * 2
def baseEnd_1114082 : Nat := 572059554522415382751437

theorem tailTrace_1114082 : CollatzResearch.WordTrace tailWord_1114082 prefixEnd_1114082 572059554522415382751437 := by
  unfold tailWord_1114082
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158477187469664725634125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27089272499919105935024333 10158477187469664725634125)
  ·
    refine ⟨3809428945301124272112797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10158477187469664725634125 3809428945301124272112797)
    ·
      refine ⟨1428535854487921602042299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3809428945301124272112797 1428535854487921602042299)
      ·
        refine ⟨2142803781731882403063449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428535854487921602042299 2142803781731882403063449)
        ·
          refine ⟨1607102836298911802297587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2142803781731882403063449 1607102836298911802297587)
          ·
            refine ⟨2410654254448367703446381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607102836298911802297587 2410654254448367703446381)
            ·
              refine ⟨903995345418137888792393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2410654254448367703446381 903995345418137888792393)
              ·
                refine ⟨677996509063603416594295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903995345418137888792393 677996509063603416594295)
                ·
                  refine ⟨1016994763595405124891443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677996509063603416594295 1016994763595405124891443)
                  ·
                    refine ⟨1525492145393107687337165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1016994763595405124891443 1525492145393107687337165)
                    ·
                      refine ⟨572059554522415382751437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1525492145393107687337165 572059554522415382751437)
                      ·
                        rfl

theorem cell23_1114082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1114082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114082 prefixEnd_1114082 := by exact prefixLift 1114082
  have htrace : WordTrace (prefixWord ++ tailWord_1114082) baseStart_1114082 baseEnd_1114082 := by
    simpa [prefixWord, tailWord_1114082, baseEnd_1114082] using wordTrace_append hprefix tailTrace_1114082
  have hstable : (prefixWord ++ tailWord_1114082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114082).length < 2 ^ (prefixWord ++ tailWord_1114082).sum := by decide
  have hdescent : baseEnd_1114082 < baseStart_1114082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114125 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1114125 : Nat := 118140960795 + 1114125 * 2 ^ 59
def prefixEnd_1114125 : Nat := 4983230072969 + 3 ^ 40 * 1114125 * 2
def baseEnd_1114125 : Nat := 572081634190558714513739

theorem tailTrace_1114125 : CollatzResearch.WordTrace tailWord_1114125 prefixEnd_1114125 572081634190558714513739 := by
  unfold tailWord_1114125
  simp only [CollatzResearch.WordTrace]
  refine ⟨40635477088722877246351829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27090318059148584830901219 40635477088722877246351829)
  ·
    refine ⟨952393994266942435461371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 40635477088722877246351829 952393994266942435461371)
    ·
      refine ⟨1428590991400413653192057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952393994266942435461371 1428590991400413653192057)
      ·
        refine ⟨1071443243550310239894043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1428590991400413653192057 1071443243550310239894043)
        ·
          refine ⟨1607164865325465359841065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071443243550310239894043 1607164865325465359841065)
          ·
            refine ⟨1205373648994099019880799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1607164865325465359841065 1205373648994099019880799)
            ·
              refine ⟨1808060473491148529821199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205373648994099019880799 1808060473491148529821199)
              ·
                refine ⟨2712090710236722794731799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808060473491148529821199 2712090710236722794731799)
                ·
                  refine ⟨4068136065355084192097699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712090710236722794731799 4068136065355084192097699)
                  ·
                    refine ⟨6102204098032626288146549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4068136065355084192097699 6102204098032626288146549)
                    ·
                      refine ⟨572081634190558714513739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6102204098032626288146549 572081634190558714513739)
                      ·
                        rfl

theorem cell23_1114125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1114125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114125 prefixEnd_1114125 := by exact prefixLift 1114125
  have htrace : WordTrace (prefixWord ++ tailWord_1114125) baseStart_1114125 baseEnd_1114125 := by
    simpa [prefixWord, tailWord_1114125, baseEnd_1114125] using wordTrace_append hprefix tailTrace_1114125
  have hstable : (prefixWord ++ tailWord_1114125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114125).length < 2 ^ (prefixWord ++ tailWord_1114125).sum := by decide
  have hdescent : baseEnd_1114125 < baseStart_1114125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114147 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 3]
def baseStart_1114147 : Nat := 118140960795 + 1114147 * 2 ^ 59
def prefixEnd_1114147 : Nat := 4983230072969 + 3 ^ 40 * 1114147 * 2
def baseEnd_1114147 : Nat := 572092930764957628438637

theorem tailTrace_1114147 : CollatzResearch.WordTrace tailWord_1114147 prefixEnd_1114147 572092930764957628438637 := by
  unfold tailWord_1114147
  simp only [CollatzResearch.WordTrace]
  refine ⟨40636279494643175003652695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27090852996428783335768463 40636279494643175003652695)
  ·
    refine ⟨60954419241964762505479043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40636279494643175003652695 60954419241964762505479043)
    ·
      refine ⟨91431628862947143758218565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60954419241964762505479043 91431628862947143758218565)
      ·
        refine ⟨17143430411802589454665981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91431628862947143758218565 17143430411802589454665981)
        ·
          refine ⟨6428786404425971045499743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17143430411802589454665981 6428786404425971045499743)
          ·
            refine ⟨9643179606638956568249615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6428786404425971045499743 9643179606638956568249615)
            ·
              refine ⟨14464769409958434852374423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9643179606638956568249615 14464769409958434852374423)
              ·
                refine ⟨21697154114937652278561635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14464769409958434852374423 21697154114937652278561635)
                ·
                  refine ⟨32545731172406478417842453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21697154114937652278561635 32545731172406478417842453)
                  ·
                    refine ⟨1525581148706553675836365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32545731172406478417842453 1525581148706553675836365)
                    ·
                      refine ⟨572092930764957628438637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1525581148706553675836365 572092930764957628438637)
                      ·
                        rfl

theorem cell23_1114147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_1114147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114147 prefixEnd_1114147 := by exact prefixLift 1114147
  have htrace : WordTrace (prefixWord ++ tailWord_1114147) baseStart_1114147 baseEnd_1114147 := by
    simpa [prefixWord, tailWord_1114147, baseEnd_1114147] using wordTrace_append hprefix tailTrace_1114147
  have hstable : (prefixWord ++ tailWord_1114147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114147).length < 2 ^ (prefixWord ++ tailWord_1114147).sum := by decide
  have hdescent : baseEnd_1114147 < baseStart_1114147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114154 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1114154 : Nat := 118140960795 + 1114154 * 2 ^ 59
def prefixEnd_1114154 : Nat := 4983230072969 + 3 ^ 40 * 1114154 * 2
def baseEnd_1114154 : Nat := 190698841709846367017035

theorem tailTrace_1114154 : CollatzResearch.WordTrace tailWord_1114154 prefixEnd_1114154 190698841709846367017035 := by
  unfold tailWord_1114154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10159133701404453799789379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27091023203745210132771677 10159133701404453799789379)
  ·
    refine ⟨15238700552106680699684069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10159133701404453799789379 15238700552106680699684069)
    ·
      refine ⟨2857256353520002631190763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15238700552106680699684069 2857256353520002631190763)
      ·
        refine ⟨4285884530280003946786145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857256353520002631190763 4285884530280003946786145)
        ·
          refine ⟨3214413397710002960089609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4285884530280003946786145 3214413397710002960089609)
          ·
            refine ⟨2410810048282502220067207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3214413397710002960089609 2410810048282502220067207)
            ·
              refine ⟨3616215072423753330100811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410810048282502220067207 3616215072423753330100811)
              ·
                refine ⟨5424322608635629995151217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616215072423753330100811 5424322608635629995151217)
                ·
                  refine ⟨4068241956476722496363413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5424322608635629995151217 4068241956476722496363413)
                  ·
                    refine ⟨190698841709846367017035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4068241956476722496363413 190698841709846367017035)
                    ·
                      rfl

theorem cell23_1114154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1114154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114154 prefixEnd_1114154 := by exact prefixLift 1114154
  have htrace : WordTrace (prefixWord ++ tailWord_1114154) baseStart_1114154 baseEnd_1114154 := by
    simpa [prefixWord, tailWord_1114154, baseEnd_1114154] using wordTrace_append hprefix tailTrace_1114154
  have hstable : (prefixWord ++ tailWord_1114154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114154).length < 2 ^ (prefixWord ++ tailWord_1114154).sum := by decide
  have hdescent : baseEnd_1114154 < baseStart_1114154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114161 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 1, 4, 2]
def baseStart_1114161 : Nat := 118140960795 + 1114161 * 2 ^ 59
def prefixEnd_1114161 : Nat := 4983230072969 + 3 ^ 40 * 1114161 * 2
def baseEnd_1114161 : Nat := 572100119494120573663573

theorem tailTrace_1114161 : CollatzResearch.WordTrace tailWord_1114161 prefixEnd_1114161 572100119494120573663573 := by
  unfold tailWord_1114161
  simp only [CollatzResearch.WordTrace]
  refine ⟨40636790116592455394662337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27091193411061636929774891 40636790116592455394662337)
  ·
    refine ⟨30477592587444341545996753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40636790116592455394662337 30477592587444341545996753)
    ·
      refine ⟨22858194440583256159497565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30477592587444341545996753 22858194440583256159497565)
      ·
        refine ⟨8571822915218721059811587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22858194440583256159497565 8571822915218721059811587)
        ·
          refine ⟨12857734372828081589717381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8571822915218721059811587 12857734372828081589717381)
          ·
            refine ⟨2410825194905265298072009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12857734372828081589717381 2410825194905265298072009)
            ·
              refine ⟨1808118896178948973554007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2410825194905265298072009 1808118896178948973554007)
              ·
                refine ⟨2712178344268423460331011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808118896178948973554007 2712178344268423460331011)
                ·
                  refine ⟨4068267516402635190496517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712178344268423460331011 4068267516402635190496517)
                  ·
                    refine ⟨762800159325494098218097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4068267516402635190496517 762800159325494098218097)
                    ·
                      refine ⟨572100119494120573663573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762800159325494098218097 572100119494120573663573)
                      ·
                        rfl

theorem cell23_1114161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_1114161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114161 prefixEnd_1114161 := by exact prefixLift 1114161
  have htrace : WordTrace (prefixWord ++ tailWord_1114161) baseStart_1114161 baseEnd_1114161 := by
    simpa [prefixWord, tailWord_1114161, baseEnd_1114161] using wordTrace_append hprefix tailTrace_1114161
  have hstable : (prefixWord ++ tailWord_1114161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114161).length < 2 ^ (prefixWord ++ tailWord_1114161).sum := by decide
  have hdescent : baseEnd_1114161 < baseStart_1114161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114217 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_1114217 : Nat := 118140960795 + 1114217 * 2 ^ 59
def prefixEnd_1114217 : Nat := 4983230072969 + 3 ^ 40 * 1114217 * 2
def baseEnd_1114217 : Nat := 572128874410772354563315

theorem tailTrace_1114217 : CollatzResearch.WordTrace tailWord_1114217 prefixEnd_1114217 572128874410772354563315 := by
  unfold tailWord_1114217
  simp only [CollatzResearch.WordTrace]
  refine ⟨40638832604389576958700905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27092555069593051305800603 40638832604389576958700905)
  ·
    refine ⟨30479124453292182719025679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40638832604389576958700905 30479124453292182719025679)
    ·
      refine ⟨45718686679938274078538519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30479124453292182719025679 45718686679938274078538519)
      ·
        refine ⟨68578030019907411117807779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45718686679938274078538519 68578030019907411117807779)
        ·
          refine ⟨102867045029861116676711669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68578030019907411117807779 102867045029861116676711669)
          ·
            refine ⟨9643785471549479688441719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102867045029861116676711669 9643785471549479688441719)
            ·
              refine ⟨14465678207324219532662579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9643785471549479688441719 14465678207324219532662579)
              ·
                refine ⟨21698517310986329298993869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14465678207324219532662579 21698517310986329298993869)
                ·
                  refine ⟨8136943991619873487122701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21698517310986329298993869 8136943991619873487122701)
                  ·
                    refine ⟨3051353996857452557671013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8136943991619873487122701 3051353996857452557671013)
                    ·
                      refine ⟨572128874410772354563315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3051353996857452557671013 572128874410772354563315)
                      ·
                        rfl

theorem cell23_1114217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_1114217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114217 prefixEnd_1114217 := by exact prefixLift 1114217
  have htrace : WordTrace (prefixWord ++ tailWord_1114217) baseStart_1114217 baseEnd_1114217 := by
    simpa [prefixWord, tailWord_1114217, baseEnd_1114217] using wordTrace_append hprefix tailTrace_1114217
  have hstable : (prefixWord ++ tailWord_1114217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114217).length < 2 ^ (prefixWord ++ tailWord_1114217).sum := by decide
  have hdescent : baseEnd_1114217 < baseStart_1114217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114247 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1114247 : Nat := 118140960795 + 1114247 * 2 ^ 59
def prefixEnd_1114247 : Nat := 4983230072969 + 3 ^ 40 * 1114247 * 2
def baseEnd_1114247 : Nat := 572144278830407237188177

theorem tailTrace_1114247 : CollatzResearch.WordTrace tailWord_1114247 prefixEnd_1114247 572144278830407237188177 := by
  unfold tailWord_1114247
  simp only [CollatzResearch.WordTrace]
  refine ⟨40639926794280892082292995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27093284529520594721528663 40639926794280892082292995)
  ·
    refine ⟨60959890191421338123439493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40639926794280892082292995 60959890191421338123439493)
    ·
      refine ⟨11429979410891500898144905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60959890191421338123439493 11429979410891500898144905)
      ·
        refine ⟨8572484558168625673608679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11429979410891500898144905 8572484558168625673608679)
        ·
          refine ⟨12858726837252938510413019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8572484558168625673608679 12858726837252938510413019)
          ·
            refine ⟨19288090255879407765619529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12858726837252938510413019 19288090255879407765619529)
            ·
              refine ⟨14466067691909555824214647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19288090255879407765619529 14466067691909555824214647)
              ·
                refine ⟨21699101537864333736321971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14466067691909555824214647 21699101537864333736321971)
                ·
                  refine ⟨32548652306796500604482957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21699101537864333736321971 32548652306796500604482957)
                  ·
                    refine ⟨12205744615048687726681109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32548652306796500604482957 12205744615048687726681109)
                    ·
                      refine ⟨572144278830407237188177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12205744615048687726681109 572144278830407237188177)
                      ·
                        rfl

theorem cell23_1114247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1114247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114247 prefixEnd_1114247 := by exact prefixLift 1114247
  have htrace : WordTrace (prefixWord ++ tailWord_1114247) baseStart_1114247 baseEnd_1114247 := by
    simpa [prefixWord, tailWord_1114247, baseEnd_1114247] using wordTrace_append hprefix tailTrace_1114247
  have hstable : (prefixWord ++ tailWord_1114247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114247).length < 2 ^ (prefixWord ++ tailWord_1114247).sum := by decide
  have hdescent : baseEnd_1114247 < baseStart_1114247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114341 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1114341 : Nat := 118140960795 + 1114341 * 2 ^ 59
def prefixEnd_1114341 : Nat := 4983230072969 + 3 ^ 40 * 1114341 * 2
def baseEnd_1114341 : Nat := 572192546011929869412745

theorem tailTrace_1114341 : CollatzResearch.WordTrace tailWord_1114341 prefixEnd_1114341 572192546011929869412745 := by
  unfold tailWord_1114341
  simp only [CollatzResearch.WordTrace]
  refine ⟨40643355255940346136214877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27095570170626897424143251 40643355255940346136214877)
  ·
    refine ⟨15241258220977629801080579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40643355255940346136214877 15241258220977629801080579)
    ·
      refine ⟨22861887331466444701620869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15241258220977629801080579 22861887331466444701620869)
      ·
        refine ⟨4286603874649958381553913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22861887331466444701620869 4286603874649958381553913)
        ·
          refine ⟨3214952905987468786165435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4286603874649958381553913 3214952905987468786165435)
          ·
            refine ⟨4822429358981203179248153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214952905987468786165435 4822429358981203179248153)
            ·
              refine ⟨3616822019235902384436115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4822429358981203179248153 3616822019235902384436115)
              ·
                refine ⟨5425233028853853576654173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616822019235902384436115 5425233028853853576654173)
                ·
                  refine ⟨2034462385820195091245315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5425233028853853576654173 2034462385820195091245315)
                  ·
                    refine ⟨3051693578730292636867973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2034462385820195091245315 3051693578730292636867973)
                    ·
                      refine ⟨572192546011929869412745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3051693578730292636867973 572192546011929869412745)
                      ·
                        rfl

theorem cell23_1114341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1114341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114341 prefixEnd_1114341 := by exact prefixLift 1114341
  have htrace : WordTrace (prefixWord ++ tailWord_1114341) baseStart_1114341 baseEnd_1114341 := by
    simpa [prefixWord, tailWord_1114341, baseEnd_1114341] using wordTrace_append hprefix tailTrace_1114341
  have hstable : (prefixWord ++ tailWord_1114341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114341).length < 2 ^ (prefixWord ++ tailWord_1114341).sum := by decide
  have hdescent : baseEnd_1114341 < baseStart_1114341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114364 : List Nat := [2, 2, 2, 1, 4, 2, 10]
def baseStart_1114364 : Nat := 118140960795 + 1114364 * 2 ^ 59
def prefixEnd_1114364 : Nat := 4983230072969 + 3 ^ 40 * 1114364 * 2
def baseEnd_1114364 : Nat := 7064251309468929375619

theorem tailTrace_1114364 : CollatzResearch.WordTrace tailWord_1114364 prefixEnd_1114364 7064251309468929375619 := by
  unfold tailWord_1114364
  simp only [CollatzResearch.WordTrace]
  refine ⟨20322097067428510532151073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27096129423238014042868097 20322097067428510532151073)
  ·
    refine ⟨15241572800571382899113305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20322097067428510532151073 15241572800571382899113305)
    ·
      refine ⟨11431179600428537174334979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15241572800571382899113305 11431179600428537174334979)
      ·
        refine ⟨17146769400642805761502469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11431179600428537174334979 17146769400642805761502469)
        ·
          refine ⟨3215019262620526080281713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17146769400642805761502469 3215019262620526080281713)
          ·
            refine ⟨2411264446965394560211285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215019262620526080281713 2411264446965394560211285)
            ·
              refine ⟨7064251309468929375619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2411264446965394560211285 7064251309468929375619)
              ·
                rfl

theorem cell23_1114364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 10].length) (baseStart_1114364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114364 prefixEnd_1114364 := by exact prefixLift 1114364
  have htrace : WordTrace (prefixWord ++ tailWord_1114364) baseStart_1114364 baseEnd_1114364 := by
    simpa [prefixWord, tailWord_1114364, baseEnd_1114364] using wordTrace_append hprefix tailTrace_1114364
  have hstable : (prefixWord ++ tailWord_1114364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114364).length < 2 ^ (prefixWord ++ tailWord_1114364).sum := by decide
  have hdescent : baseEnd_1114364 < baseStart_1114364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114398 : List Nat := [4, 3, 2, 1, 1, 2, 1, 9]
def baseStart_1114398 : Nat := 118140960795 + 1114398 * 2 ^ 59
def prefixEnd_1114398 : Nat := 4983230072969 + 3 ^ 40 * 1114398 * 2
def baseEnd_1114398 : Nat := 21193400533675412829629

theorem tailTrace_1114398 : CollatzResearch.WordTrace tailWord_1114398 prefixEnd_1114398 21193400533675412829629 := by
  unfold tailWord_1114398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080679277091730608879981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27096956144489229914026565 5080679277091730608879981)
  ·
    refine ⟨1905254728909398978329993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5080679277091730608879981 1905254728909398978329993)
    ·
      refine ⟨1428941046682049233747495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1905254728909398978329993 1428941046682049233747495)
      ·
        refine ⟨2143411570023073850621243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428941046682049233747495 2143411570023073850621243)
        ·
          refine ⟨3215117355034610775931865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2143411570023073850621243 3215117355034610775931865)
          ·
            refine ⟨2411338016275958081948899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215117355034610775931865 2411338016275958081948899)
            ·
              refine ⟨3617007024413937122923349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411338016275958081948899 3617007024413937122923349)
              ·
                refine ⟨21193400533675412829629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3617007024413937122923349 21193400533675412829629)
                ·
                  rfl

theorem cell23_1114398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_1114398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114398 prefixEnd_1114398 := by exact prefixLift 1114398
  have htrace : WordTrace (prefixWord ++ tailWord_1114398) baseStart_1114398 baseEnd_1114398 := by
    simpa [prefixWord, tailWord_1114398, baseEnd_1114398] using wordTrace_append hprefix tailTrace_1114398
  have hstable : (prefixWord ++ tailWord_1114398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114398).length < 2 ^ (prefixWord ++ tailWord_1114398).sum := by decide
  have hdescent : baseEnd_1114398 < baseStart_1114398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114424 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 4, 6]
def baseStart_1114424 : Nat := 118140960795 + 1114424 * 2 ^ 59
def prefixEnd_1114424 : Nat := 4983230072969 + 3 ^ 40 * 1114424 * 2
def baseEnd_1114424 : Nat := 190745054968751014891621

theorem tailTrace_1114424 : CollatzResearch.WordTrace tailWord_1114424 prefixEnd_1114424 190745054968751014891621 := by
  unfold tailWord_1114424
  simp only [CollatzResearch.WordTrace]
  refine ⟨20323191257319825655743163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27097588343093100874324217 20323191257319825655743163)
  ·
    refine ⟨30484786885979738483614745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20323191257319825655743163 30484786885979738483614745)
    ·
      refine ⟨22863590164484803862711059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30484786885979738483614745 22863590164484803862711059)
      ·
        refine ⟨34295385246727205794066589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22863590164484803862711059 34295385246727205794066589)
        ·
          refine ⟨12860769467522702172774971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34295385246727205794066589 12860769467522702172774971)
          ·
            refine ⟨19291154201284053259162457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12860769467522702172774971 19291154201284053259162457)
            ·
              refine ⟨14468365650963039944371843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19291154201284053259162457 14468365650963039944371843)
              ·
                refine ⟨21702548476444559916557765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14468365650963039944371843 21702548476444559916557765)
                ·
                  refine ⟨4069227839333354984354581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21702548476444559916557765 4069227839333354984354581)
                  ·
                    refine ⟨190745054968751014891621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4069227839333354984354581 190745054968751014891621)
                    ·
                      rfl

theorem cell23_1114424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_1114424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114424 prefixEnd_1114424 := by exact prefixLift 1114424
  have htrace : WordTrace (prefixWord ++ tailWord_1114424) baseStart_1114424 baseEnd_1114424 := by
    simpa [prefixWord, tailWord_1114424, baseEnd_1114424] using wordTrace_append hprefix tailTrace_1114424
  have hstable : (prefixWord ++ tailWord_1114424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114424).length < 2 ^ (prefixWord ++ tailWord_1114424).sum := by decide
  have hdescent : baseEnd_1114424 < baseStart_1114424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114452 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_1114452 : Nat := 118140960795 + 1114452 * 2 ^ 59
def prefixEnd_1114452 : Nat := 4983230072969 + 3 ^ 40 * 1114452 * 2
def baseEnd_1114452 : Nat := 572249542364578935124735

theorem tailTrace_1114452 : CollatzResearch.WordTrace tailWord_1114452 prefixEnd_1114452 572249542364578935124735 := by
  unfold tailWord_1114452
  simp only [CollatzResearch.WordTrace]
  refine ⟨20323701879269106046752805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27098269172358808062337073 20323701879269106046752805)
  ·
    refine ⟨3810694102362957383766151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20323701879269106046752805 3810694102362957383766151)
    ·
      refine ⟨5716041153544436075649227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3810694102362957383766151 5716041153544436075649227)
      ·
        refine ⟨8574061730316654113473841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716041153544436075649227 8574061730316654113473841)
        ·
          refine ⟨6430546297737490585105381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8574061730316654113473841 6430546297737490585105381)
          ·
            refine ⟨1205727430825779484707259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6430546297737490585105381 1205727430825779484707259)
            ·
              refine ⟨1808591146238669227060889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205727430825779484707259 1808591146238669227060889)
              ·
                refine ⟨1356443359679001920295667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808591146238669227060889 1356443359679001920295667)
                ·
                  refine ⟨2034665039518502880443501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356443359679001920295667 2034665039518502880443501)
                  ·
                    refine ⟨762999389819438580166313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034665039518502880443501 762999389819438580166313)
                    ·
                      refine ⟨572249542364578935124735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 762999389819438580166313 572249542364578935124735)
                      ·
                        rfl

theorem cell23_1114452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_1114452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114452 prefixEnd_1114452 := by exact prefixLift 1114452
  have htrace : WordTrace (prefixWord ++ tailWord_1114452) baseStart_1114452 baseEnd_1114452 := by
    simpa [prefixWord, tailWord_1114452, baseEnd_1114452] using wordTrace_append hprefix tailTrace_1114452
  have hstable : (prefixWord ++ tailWord_1114452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114452).length < 2 ^ (prefixWord ++ tailWord_1114452).sum := by decide
  have hdescent : baseEnd_1114452 < baseStart_1114452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114481 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_1114481 : Nat := 118140960795 + 1114481 * 2 ^ 59
def prefixEnd_1114481 : Nat := 4983230072969 + 3 ^ 40 * 1114481 * 2
def baseEnd_1114481 : Nat := 572264433303559321662101

theorem tailTrace_1114481 : CollatzResearch.WordTrace tailWord_1114481 prefixEnd_1114481 572264433303559321662101 := by
  unfold tailWord_1114481
  simp only [CollatzResearch.WordTrace]
  refine ⟨40648461475433150046311297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27098974316955433364207531 40648461475433150046311297)
  ·
    refine ⟨30486346106574862534733473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40648461475433150046311297 30486346106574862534733473)
    ·
      refine ⟨22864759579931146901050105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30486346106574862534733473 22864759579931146901050105)
      ·
        refine ⟨17148569684948360175787579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22864759579931146901050105 17148569684948360175787579)
        ·
          refine ⟨25722854527422540263681369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17148569684948360175787579 25722854527422540263681369)
          ·
            refine ⟨19292140895566905197761027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25722854527422540263681369 19292140895566905197761027)
            ·
              refine ⟨28938211343350357796641541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19292140895566905197761027 28938211343350357796641541)
              ·
                refine ⟨5425914626878192086870289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28938211343350357796641541 5425914626878192086870289)
                ·
                  refine ⟨4069435970158644065152717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5425914626878192086870289 4069435970158644065152717)
                  ·
                    refine ⟨1526038488809491524432269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4069435970158644065152717 1526038488809491524432269)
                    ·
                      refine ⟨572264433303559321662101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526038488809491524432269 572264433303559321662101)
                      ·
                        rfl

theorem cell23_1114481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_1114481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114481 prefixEnd_1114481 := by exact prefixLift 1114481
  have htrace : WordTrace (prefixWord ++ tailWord_1114481) baseStart_1114481 baseEnd_1114481 := by
    simpa [prefixWord, tailWord_1114481, baseEnd_1114481] using wordTrace_append hprefix tailTrace_1114481
  have hstable : (prefixWord ++ tailWord_1114481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114481).length < 2 ^ (prefixWord ++ tailWord_1114481).sum := by decide
  have hdescent : baseEnd_1114481 < baseStart_1114481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114482 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_1114482 : Nat := 118140960795 + 1114482 * 2 ^ 59
def prefixEnd_1114482 : Nat := 4983230072969 + 3 ^ 40 * 1114482 * 2
def baseEnd_1114482 : Nat := 572264946784213817749597

theorem tailTrace_1114482 : CollatzResearch.WordTrace tailWord_1114482 prefixEnd_1114482 572264946784213817749597 := by
  unfold tailWord_1114482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10162124487107381804274425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27098998632286351478065133 10162124487107381804274425)
  ·
    refine ⟨7621593365330536353205819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10162124487107381804274425 7621593365330536353205819)
    ·
      refine ⟨11432390047995804529808729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7621593365330536353205819 11432390047995804529808729)
      ·
        refine ⟨8574292535996853397356547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11432390047995804529808729 8574292535996853397356547)
        ·
          refine ⟨12861438803995280096034821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8574292535996853397356547 12861438803995280096034821)
          ·
            refine ⟨2411519775749115018006529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12861438803995280096034821 2411519775749115018006529)
            ·
              refine ⟨1808639831811836263504897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2411519775749115018006529 1808639831811836263504897)
              ·
                refine ⟨1356479873858877197628673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808639831811836263504897 1356479873858877197628673)
                ·
                  refine ⟨1017359905394157898221505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1356479873858877197628673 1017359905394157898221505)
                  ·
                    refine ⟨763019929045618423666129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1017359905394157898221505 763019929045618423666129)
                    ·
                      refine ⟨572264946784213817749597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763019929045618423666129 572264946784213817749597)
                      ·
                        rfl

theorem cell23_1114482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_1114482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114482 prefixEnd_1114482 := by exact prefixLift 1114482
  have htrace : WordTrace (prefixWord ++ tailWord_1114482) baseStart_1114482 baseEnd_1114482 := by
    simpa [prefixWord, tailWord_1114482, baseEnd_1114482] using wordTrace_append hprefix tailTrace_1114482
  have hstable : (prefixWord ++ tailWord_1114482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114482).length < 2 ^ (prefixWord ++ tailWord_1114482).sum := by decide
  have hdescent : baseEnd_1114482 < baseStart_1114482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114521 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_1114521 : Nat := 118140960795 + 1114521 * 2 ^ 59
def prefixEnd_1114521 : Nat := 4983230072969 + 3 ^ 40 * 1114521 * 2
def baseEnd_1114521 : Nat := 572284972529739165161917

theorem tailTrace_1114521 : CollatzResearch.WordTrace tailWord_1114521 prefixEnd_1114521 572284972529739165161917 := by
  unfold tailWord_1114521
  simp only [CollatzResearch.WordTrace]
  refine ⟨40649920395288236877767417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27099946930192157918511611 40649920395288236877767417)
  ·
    refine ⟨30487440296466177658325563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40649920395288236877767417 30487440296466177658325563)
    ·
      refine ⟨45731160444699266487488345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30487440296466177658325563 45731160444699266487488345)
      ·
        refine ⟨34298370333524449865616259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45731160444699266487488345 34298370333524449865616259)
        ·
          refine ⟨51447555500286674798424389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34298370333524449865616259 51447555500286674798424389)
          ·
            refine ⟨9646416656303751524704573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51447555500286674798424389 9646416656303751524704573)
            ·
              refine ⟨3617406246113906821764215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9646416656303751524704573 3617406246113906821764215)
              ·
                refine ⟨5426109369170860232646323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617406246113906821764215 5426109369170860232646323)
                ·
                  refine ⟨8139164053756290348969485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5426109369170860232646323 8139164053756290348969485)
                  ·
                    refine ⟨3052186520158608880863557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8139164053756290348969485 3052186520158608880863557)
                    ·
                      refine ⟨572284972529739165161917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3052186520158608880863557 572284972529739165161917)
                      ·
                        rfl

theorem cell23_1114521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_1114521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114521 prefixEnd_1114521 := by exact prefixLift 1114521
  have htrace : WordTrace (prefixWord ++ tailWord_1114521) baseStart_1114521 baseEnd_1114521 := by
    simpa [prefixWord, tailWord_1114521, baseEnd_1114521] using wordTrace_append hprefix tailTrace_1114521
  have hstable : (prefixWord ++ tailWord_1114521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114521).length < 2 ^ (prefixWord ++ tailWord_1114521).sum := by decide
  have hdescent : baseEnd_1114521 < baseStart_1114521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114558 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1114558 : Nat := 118140960795 + 1114558 * 2 ^ 59
def prefixEnd_1114558 : Nat := 4983230072969 + 3 ^ 40 * 1114558 * 2
def baseEnd_1114558 : Nat := 572303971313955520399247

theorem tailTrace_1114558 : CollatzResearch.WordTrace tailWord_1114558 prefixEnd_1114558 572303971313955520399247 := by
  unfold tailWord_1114558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5081408737019274024608041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27100846597436128131242885 5081408737019274024608041)
  ·
    refine ⟨3811056552764455518456031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5081408737019274024608041 3811056552764455518456031)
    ·
      refine ⟨5716584829146683277684047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3811056552764455518456031 5716584829146683277684047)
      ·
        refine ⟨8574877243720024916526071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716584829146683277684047 8574877243720024916526071)
        ·
          refine ⟨12862315865580037374789107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8574877243720024916526071 12862315865580037374789107)
          ·
            refine ⟨19293473798370056062183661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12862315865580037374789107 19293473798370056062183661)
            ·
              refine ⟨7235052674388771023318873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19293473798370056062183661 7235052674388771023318873)
              ·
                refine ⟨5426289505791578267489155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7235052674388771023318873 5426289505791578267489155)
                ·
                  refine ⟨8139434258687367401233733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5426289505791578267489155 8139434258687367401233733)
                  ·
                    refine ⟨1526143923503881387731325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8139434258687367401233733 1526143923503881387731325)
                    ·
                      refine ⟨572303971313955520399247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526143923503881387731325 572303971313955520399247)
                      ·
                        rfl

theorem cell23_1114558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1114558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114558 prefixEnd_1114558 := by exact prefixLift 1114558
  have htrace : WordTrace (prefixWord ++ tailWord_1114558) baseStart_1114558 baseEnd_1114558 := by
    simpa [prefixWord, tailWord_1114558, baseEnd_1114558] using wordTrace_append hprefix tailTrace_1114558
  have hstable : (prefixWord ++ tailWord_1114558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114558).length < 2 ^ (prefixWord ++ tailWord_1114558).sum := by decide
  have hdescent : baseEnd_1114558 < baseStart_1114558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114571 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 3]
def baseStart_1114571 : Nat := 118140960795 + 1114571 * 2 ^ 59
def prefixEnd_1114571 : Nat := 4983230072969 + 3 ^ 40 * 1114571 * 2
def baseEnd_1114571 : Nat := 572310646562463969536687

theorem tailTrace_1114571 : CollatzResearch.WordTrace tailWord_1114571 prefixEnd_1114571 572310646562463969536687 := by
  unfold tailWord_1114571
  simp only [CollatzResearch.WordTrace]
  refine ⟨40651744045107095417087567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27101162696738063611391711 40651744045107095417087567)
  ·
    refine ⟨60977616067660643125631351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40651744045107095417087567 60977616067660643125631351)
    ·
      refine ⟨91466424101490964688447027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60977616067660643125631351 91466424101490964688447027)
      ·
        refine ⟨137199636152236447032670541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91466424101490964688447027 137199636152236447032670541)
        ·
          refine ⟨51449863557088667637251453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137199636152236447032670541 51449863557088667637251453)
          ·
            refine ⟨19293698833908250363969295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51449863557088667637251453 19293698833908250363969295)
            ·
              refine ⟨28940548250862375545953943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19293698833908250363969295 28940548250862375545953943)
              ·
                refine ⟨43410822376293563318930915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28940548250862375545953943 43410822376293563318930915)
                ·
                  refine ⟨65116233564440344978396373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43410822376293563318930915 65116233564440344978396373)
                  ·
                    refine ⟨1526161724166570585431165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65116233564440344978396373 1526161724166570585431165)
                    ·
                      refine ⟨572310646562463969536687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526161724166570585431165 572310646562463969536687)
                      ·
                        rfl

theorem cell23_1114571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 3].length) (baseStart_1114571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114571 prefixEnd_1114571 := by exact prefixLift 1114571
  have htrace : WordTrace (prefixWord ++ tailWord_1114571) baseStart_1114571 baseEnd_1114571 := by
    simpa [prefixWord, tailWord_1114571, baseEnd_1114571] using wordTrace_append hprefix tailTrace_1114571
  have hstable : (prefixWord ++ tailWord_1114571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114571).length < 2 ^ (prefixWord ++ tailWord_1114571).sum := by decide
  have hdescent : baseEnd_1114571 < baseStart_1114571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114625 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1114625 : Nat := 118140960795 + 1114625 * 2 ^ 59
def prefixEnd_1114625 : Nat := 4983230072969 + 3 ^ 40 * 1114625 * 2
def baseEnd_1114625 : Nat := 190779458172602252753813

theorem tailTrace_1114625 : CollatzResearch.WordTrace tailWord_1114625 prefixEnd_1114625 190779458172602252753813 := by
  unfold tailWord_1114625
  simp only [CollatzResearch.WordTrace]
  refine ⟨40653713586911462639553329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27102475724607641759702219 40653713586911462639553329)
  ·
    refine ⟨30490285190183596979664997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40653713586911462639553329 30490285190183596979664997)
    ·
      refine ⟨5716928473159424433687187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30490285190183596979664997 5716928473159424433687187)
      ·
        refine ⟨8575392709739136650530781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716928473159424433687187 8575392709739136650530781)
        ·
          refine ⟨3215772266152176243949043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8575392709739136650530781 3215772266152176243949043)
          ·
            refine ⟨4823658399228264365923565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3215772266152176243949043 4823658399228264365923565)
            ·
              refine ⟨1808871899710599137221337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4823658399228264365923565 1808871899710599137221337)
              ·
                refine ⟨1356653924782949352916003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808871899710599137221337 1356653924782949352916003)
                ·
                  refine ⟨2034980887174424029374005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356653924782949352916003 2034980887174424029374005)
                  ·
                    refine ⟨190779458172602252753813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2034980887174424029374005 190779458172602252753813)
                    ·
                      rfl

theorem cell23_1114625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1114625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114625 prefixEnd_1114625 := by exact prefixLift 1114625
  have htrace : WordTrace (prefixWord ++ tailWord_1114625) baseStart_1114625 baseEnd_1114625 := by
    simpa [prefixWord, tailWord_1114625, baseEnd_1114625] using wordTrace_append hprefix tailTrace_1114625
  have hstable : (prefixWord ++ tailWord_1114625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114625).length < 2 ^ (prefixWord ++ tailWord_1114625).sum := by decide
  have hdescent : baseEnd_1114625 < baseStart_1114625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114638 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_1114638 : Nat := 118140960795 + 1114638 * 2 ^ 59
def prefixEnd_1114638 : Nat := 4983230072969 + 3 ^ 40 * 1114638 * 2
def baseEnd_1114638 : Nat := 190781683255438402466293

theorem tailTrace_1114638 : CollatzResearch.WordTrace tailWord_1114638 prefixEnd_1114638 190781683255438402466293 := by
  unfold tailWord_1114638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5081773466983045732472071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27102791823909577239851045 5081773466983045732472071)
  ·
    refine ⟨7622660200474568598708107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5081773466983045732472071 7622660200474568598708107)
    ·
      refine ⟨11433990300711852898062161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7622660200474568598708107 11433990300711852898062161)
      ·
        refine ⟨8575492725533889673546621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11433990300711852898062161 8575492725533889673546621)
        ·
          refine ⟨3215809772075208627579983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8575492725533889673546621 3215809772075208627579983)
          ·
            refine ⟨4823714658112812941369975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3215809772075208627579983 4823714658112812941369975)
            ·
              refine ⟨7235571987169219412054963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4823714658112812941369975 7235571987169219412054963)
              ·
                refine ⟨10853357980753829118082445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7235571987169219412054963 10853357980753829118082445)
                ·
                  refine ⟨4070009242782685919280917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10853357980753829118082445 4070009242782685919280917)
                  ·
                    refine ⟨190781683255438402466293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4070009242782685919280917 190781683255438402466293)
                    ·
                      rfl

theorem cell23_1114638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_1114638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114638 prefixEnd_1114638 := by exact prefixLift 1114638
  have htrace : WordTrace (prefixWord ++ tailWord_1114638) baseStart_1114638 baseEnd_1114638 := by
    simpa [prefixWord, tailWord_1114638, baseEnd_1114638] using wordTrace_append hprefix tailTrace_1114638
  have hstable : (prefixWord ++ tailWord_1114638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114638).length < 2 ^ (prefixWord ++ tailWord_1114638).sum := by decide
  have hdescent : baseEnd_1114638 < baseStart_1114638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114641 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_1114641 : Nat := 118140960795 + 1114641 * 2 ^ 59
def prefixEnd_1114641 : Nat := 4983230072969 + 3 ^ 40 * 1114641 * 2
def baseEnd_1114641 : Nat := 572346590208278695661365

theorem tailTrace_1114641 : CollatzResearch.WordTrace tailWord_1114641 prefixEnd_1114641 572346590208278695661365 := by
  unfold tailWord_1114641
  simp only [CollatzResearch.WordTrace]
  refine ⟨40654297154853497372135777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27102864769902331581423851 40654297154853497372135777)
  ·
    refine ⟨30490722866140123029101833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40654297154853497372135777 30490722866140123029101833)
    ·
      refine ⟨22868042149605092271826375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30490722866140123029101833 22868042149605092271826375)
      ·
        refine ⟨34302063224407638407739563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22868042149605092271826375 34302063224407638407739563)
        ·
          refine ⟨51453094836611457611609345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34302063224407638407739563 51453094836611457611609345)
          ·
            refine ⟨38589821127458593208707009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51453094836611457611609345 38589821127458593208707009)
            ·
              refine ⟨28942365845593944906530257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38589821127458593208707009 28942365845593944906530257)
              ·
                refine ⟨21706774384195458679897693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28942365845593944906530257 21706774384195458679897693)
                ·
                  refine ⟨8140040394073297004961635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21706774384195458679897693 8140040394073297004961635)
                  ·
                    refine ⟨12210060591109945507442453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8140040394073297004961635 12210060591109945507442453)
                    ·
                      refine ⟨572346590208278695661365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12210060591109945507442453 572346590208278695661365)
                      ·
                        rfl

theorem cell23_1114641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_1114641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114641 prefixEnd_1114641 := by exact prefixLift 1114641
  have htrace : WordTrace (prefixWord ++ tailWord_1114641) baseStart_1114641 baseEnd_1114641 := by
    simpa [prefixWord, tailWord_1114641, baseEnd_1114641] using wordTrace_append hprefix tailTrace_1114641
  have hstable : (prefixWord ++ tailWord_1114641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114641).length < 2 ^ (prefixWord ++ tailWord_1114641).sum := by decide
  have hdescent : baseEnd_1114641 < baseStart_1114641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114658 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1114658 : Nat := 118140960795 + 1114658 * 2 ^ 59
def prefixEnd_1114658 : Nat := 4983230072969 + 3 ^ 40 * 1114658 * 2
def baseEnd_1114658 : Nat := 572355319379405129148787

theorem tailTrace_1114658 : CollatzResearch.WordTrace tailWord_1114658 prefixEnd_1114658 572355319379405129148787 := by
  unfold tailWord_1114658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10163729298947977318876157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27103278130527939517003085 10163729298947977318876157)
  ·
    refine ⟨3811398487105491494578559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10163729298947977318876157 3811398487105491494578559)
    ·
      refine ⟨5717097730658237241867839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3811398487105491494578559 5717097730658237241867839)
      ·
        refine ⟨8575646595987355862801759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5717097730658237241867839 8575646595987355862801759)
        ·
          refine ⟨12863469893981033794202639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8575646595987355862801759 12863469893981033794202639)
          ·
            refine ⟨19295204840971550691303959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12863469893981033794202639 19295204840971550691303959)
            ·
              refine ⟨28942807261457326036955939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19295204840971550691303959 28942807261457326036955939)
              ·
                refine ⟨43414210892185989055433909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28942807261457326036955939 43414210892185989055433909)
                ·
                  refine ⟨4070082271142436473946929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43414210892185989055433909 4070082271142436473946929)
                  ·
                    refine ⟨3052561703356827355460197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4070082271142436473946929 3052561703356827355460197)
                    ·
                      refine ⟨572355319379405129148787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3052561703356827355460197 572355319379405129148787)
                      ·
                        rfl

theorem cell23_1114658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1114658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114658 prefixEnd_1114658 := by exact prefixLift 1114658
  have htrace : WordTrace (prefixWord ++ tailWord_1114658) baseStart_1114658 baseEnd_1114658 := by
    simpa [prefixWord, tailWord_1114658, baseEnd_1114658] using wordTrace_append hprefix tailTrace_1114658
  have hstable : (prefixWord ++ tailWord_1114658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114658).length < 2 ^ (prefixWord ++ tailWord_1114658).sum := by decide
  have hdescent : baseEnd_1114658 < baseStart_1114658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114685 : List Nat := [1, 4, 1, 3, 2, 2, 3, 7]
def baseStart_1114685 : Nat := 118140960795 + 1114685 * 2 ^ 59
def prefixEnd_1114685 : Nat := 4983230072969 + 3 ^ 40 * 1114685 * 2
def baseEnd_1114685 : Nat := 21198858642854686055969

theorem tailTrace_1114685 : CollatzResearch.WordTrace tailWord_1114685 prefixEnd_1114685 21198858642854686055969 := by
  unfold tailWord_1114685
  simp only [CollatzResearch.WordTrace]
  refine ⟨40655901966694092886737509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27103934644462728591158339 40655901966694092886737509)
  ·
    refine ⟨7622981618755142416263283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40655901966694092886737509 7622981618755142416263283)
    ·
      refine ⟨11434472428132713624394925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7622981618755142416263283 11434472428132713624394925)
      ·
        refine ⟨4287927160549767609148097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11434472428132713624394925 4287927160549767609148097)
        ·
          refine ⟨3215945370412325706861073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4287927160549767609148097 3215945370412325706861073)
          ·
            refine ⟨2411959027809244280145805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215945370412325706861073 2411959027809244280145805)
            ·
              refine ⟨904484635428466605054677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2411959027809244280145805 904484635428466605054677)
              ·
                refine ⟨21198858642854686055969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 904484635428466605054677 21198858642854686055969)
                ·
                  rfl

theorem cell23_1114685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 7].length) (baseStart_1114685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114685 prefixEnd_1114685 := by exact prefixLift 1114685
  have htrace : WordTrace (prefixWord ++ tailWord_1114685) baseStart_1114685 baseEnd_1114685 := by
    simpa [prefixWord, tailWord_1114685, baseEnd_1114685] using wordTrace_append hprefix tailTrace_1114685
  have hstable : (prefixWord ++ tailWord_1114685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114685).length < 2 ^ (prefixWord ++ tailWord_1114685).sum := by decide
  have hdescent : baseEnd_1114685 < baseStart_1114685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114695 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_1114695 : Nat := 118140960795 + 1114695 * 2 ^ 59
def prefixEnd_1114695 : Nat := 4983230072969 + 3 ^ 40 * 1114695 * 2
def baseEnd_1114695 : Nat := 572374318163621484386117

theorem tailTrace_1114695 : CollatzResearch.WordTrace tailWord_1114695 prefixEnd_1114695 572374318163621484386117 := by
  unfold tailWord_1114695
  simp only [CollatzResearch.WordTrace]
  refine ⟨40656266696657864594601539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27104177797771909729734359 40656266696657864594601539)
  ·
    refine ⟨60984400044986796891902309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40656266696657864594601539 60984400044986796891902309)
    ·
      refine ⟨11434575008435024417231683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60984400044986796891902309 11434575008435024417231683)
      ·
        refine ⟨17151862512652536625847525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11434575008435024417231683 17151862512652536625847525)
        ·
          refine ⟨3215974221122350617346411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17151862512652536625847525 3215974221122350617346411)
          ·
            refine ⟨4823961331683525926019617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3215974221122350617346411 4823961331683525926019617)
            ·
              refine ⟨3617970998762644444514713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4823961331683525926019617 3617970998762644444514713)
              ·
                refine ⟨2713478249071983333386035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3617970998762644444514713 2713478249071983333386035)
                ·
                  refine ⟨4070217373607975000079053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713478249071983333386035 4070217373607975000079053)
                  ·
                    refine ⟨1526331515102990625029645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4070217373607975000079053 1526331515102990625029645)
                    ·
                      refine ⟨572374318163621484386117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526331515102990625029645 572374318163621484386117)
                      ·
                        rfl

theorem cell23_1114695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_1114695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114695 prefixEnd_1114695 := by exact prefixLift 1114695
  have htrace : WordTrace (prefixWord ++ tailWord_1114695) baseStart_1114695 baseEnd_1114695 := by
    simpa [prefixWord, tailWord_1114695, baseEnd_1114695] using wordTrace_append hprefix tailTrace_1114695
  have hstable : (prefixWord ++ tailWord_1114695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114695).length < 2 ^ (prefixWord ++ tailWord_1114695).sum := by decide
  have hdescent : baseEnd_1114695 < baseStart_1114695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114712 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_1114712 : Nat := 118140960795 + 1114712 * 2 ^ 59
def prefixEnd_1114712 : Nat := 4983230072969 + 3 ^ 40 * 1114712 * 2
def baseEnd_1114712 : Nat := 572383047334747917873539

theorem tailTrace_1114712 : CollatzResearch.WordTrace tailWord_1114712 prefixEnd_1114712 572383047334747917873539 := by
  unfold tailWord_1114712
  simp only [CollatzResearch.WordTrace]
  refine ⟨20328443368798138248985195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27104591158397517665313593 20328443368798138248985195)
  ·
    refine ⟨30492665053197207373477793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20328443368798138248985195 30492665053197207373477793)
    ·
      refine ⟨22869498789897905530108345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30492665053197207373477793 22869498789897905530108345)
      ·
        refine ⟨17152124092423429147581259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22869498789897905530108345 17152124092423429147581259)
        ·
          refine ⟨25728186138635143721371889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17152124092423429147581259 25728186138635143721371889)
          ·
            refine ⟨19296139603976357791028917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25728186138635143721371889 19296139603976357791028917)
            ·
              refine ⟨1809013087872783542908961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19296139603976357791028917 1809013087872783542908961)
              ·
                refine ⟨1356759815904587657181721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1809013087872783542908961 1356759815904587657181721)
                ·
                  refine ⟨1017569861928440742886291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1356759815904587657181721 1017569861928440742886291)
                  ·
                    refine ⟨1526354792892661114329437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1017569861928440742886291 1526354792892661114329437)
                    ·
                      refine ⟨572383047334747917873539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526354792892661114329437 572383047334747917873539)
                      ·
                        rfl

theorem cell23_1114712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_1114712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114712 prefixEnd_1114712 := by exact prefixLift 1114712
  have htrace : WordTrace (prefixWord ++ tailWord_1114712) baseStart_1114712 baseEnd_1114712 := by
    simpa [prefixWord, tailWord_1114712, baseEnd_1114712] using wordTrace_append hprefix tailTrace_1114712
  have hstable : (prefixWord ++ tailWord_1114712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114712).length < 2 ^ (prefixWord ++ tailWord_1114712).sum := by decide
  have hdescent : baseEnd_1114712 < baseStart_1114712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114748 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_1114748 : Nat := 118140960795 + 1114748 * 2 ^ 59
def prefixEnd_1114748 : Nat := 4983230072969 + 3 ^ 40 * 1114748 * 2
def baseEnd_1114748 : Nat := 572401532638309777023373

theorem tailTrace_1114748 : CollatzResearch.WordTrace tailWord_1114748 prefixEnd_1114748 572401532638309777023373 := by
  unfold tailWord_1114748
  simp only [CollatzResearch.WordTrace]
  refine ⟨20329099882732927323140449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27105466510310569764187265 20329099882732927323140449)
  ·
    refine ⟨15246824912049695492355337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20329099882732927323140449 15246824912049695492355337)
    ·
      refine ⟨11435118684037271619266503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15246824912049695492355337 11435118684037271619266503)
      ·
        refine ⟨17152678026055907428899755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11435118684037271619266503 17152678026055907428899755)
        ·
          refine ⟨25729017039083861143349633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17152678026055907428899755 25729017039083861143349633)
          ·
            refine ⟨19296762779312895857512225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25729017039083861143349633 19296762779312895857512225)
            ·
              refine ⟨14472572084484671893134169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19296762779312895857512225 14472572084484671893134169)
              ·
                refine ⟨10854429063363503919850627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14472572084484671893134169 10854429063363503919850627)
                ·
                  refine ⟨16281643595045255879775941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10854429063363503919850627 16281643595045255879775941)
                  ·
                    refine ⟨3052808174070985477457989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16281643595045255879775941 3052808174070985477457989)
                    ·
                      refine ⟨572401532638309777023373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3052808174070985477457989 572401532638309777023373)
                      ·
                        rfl

theorem cell23_1114748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_1114748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114748 prefixEnd_1114748 := by exact prefixLift 1114748
  have htrace : WordTrace (prefixWord ++ tailWord_1114748) baseStart_1114748 baseEnd_1114748 := by
    simpa [prefixWord, tailWord_1114748, baseEnd_1114748] using wordTrace_append hprefix tailTrace_1114748
  have hstable : (prefixWord ++ tailWord_1114748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114748).length < 2 ^ (prefixWord ++ tailWord_1114748).sum := by decide
  have hdescent : baseEnd_1114748 < baseStart_1114748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114752 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 4, 2, 2]
def baseStart_1114752 : Nat := 118140960795 + 1114752 * 2 ^ 59
def prefixEnd_1114752 : Nat := 4983230072969 + 3 ^ 40 * 1114752 * 2
def baseEnd_1114752 : Nat := 572403586560927761373355

theorem tailTrace_1114752 : CollatzResearch.WordTrace tailWord_1114752 prefixEnd_1114752 572403586560927761373355 := by
  unfold tailWord_1114752
  simp only [CollatzResearch.WordTrace]
  refine ⟨20329172828725681664713255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27105563771634242219617673 20329172828725681664713255)
  ·
    refine ⟨30493759243088522497069883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20329172828725681664713255 30493759243088522497069883)
    ·
      refine ⟨45740638864632783745604825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30493759243088522497069883 45740638864632783745604825)
      ·
        refine ⟨34305479148474587809203619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45740638864632783745604825 34305479148474587809203619)
        ·
          refine ⟨51458218722711881713805429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34305479148474587809203619 51458218722711881713805429)
          ·
            refine ⟨4824208005254238910669259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51458218722711881713805429 4824208005254238910669259)
            ·
              refine ⟨7236312007881358366003889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4824208005254238910669259 7236312007881358366003889)
              ·
                refine ⟨5427234005911018774502917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7236312007881358366003889 5427234005911018774502917)
                ·
                  refine ⟨1017606376108316020219297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5427234005911018774502917 1017606376108316020219297)
                  ·
                    refine ⟨763204782081237015164473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1017606376108316020219297 763204782081237015164473)
                    ·
                      refine ⟨572403586560927761373355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763204782081237015164473 572403586560927761373355)
                      ·
                        rfl

theorem cell23_1114752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_1114752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114752 prefixEnd_1114752 := by exact prefixLift 1114752
  have htrace : WordTrace (prefixWord ++ tailWord_1114752) baseStart_1114752 baseEnd_1114752 := by
    simpa [prefixWord, tailWord_1114752, baseEnd_1114752] using wordTrace_append hprefix tailTrace_1114752
  have hstable : (prefixWord ++ tailWord_1114752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114752).length < 2 ^ (prefixWord ++ tailWord_1114752).sum := by decide
  have hdescent : baseEnd_1114752 < baseStart_1114752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114825 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 5, 6, 2]
def baseStart_1114825 : Nat := 118140960795 + 1114825 * 2 ^ 59
def prefixEnd_1114825 : Nat := 4983230072969 + 3 ^ 40 * 1114825 * 2
def baseEnd_1114825 : Nat := 572441070648705975760519

theorem tailTrace_1114825 : CollatzResearch.WordTrace tailWord_1114825 prefixEnd_1114825 572441070648705975760519 := by
  unfold tailWord_1114825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40661008186186896796833929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27107338790791264531222619 40661008186186896796833929)
  ·
    refine ⟨30495756139640172597625447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40661008186186896796833929 30495756139640172597625447)
    ·
      refine ⟨45743634209460258896438171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30495756139640172597625447 45743634209460258896438171)
      ·
        refine ⟨68615451314190388344657257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45743634209460258896438171 68615451314190388344657257)
        ·
          refine ⟨51461588485642791258492943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68615451314190388344657257 51461588485642791258492943)
          ·
            refine ⟨77192382728464186887739415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51461588485642791258492943 77192382728464186887739415)
            ·
              refine ⟨115788574092696280331609123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77192382728464186887739415 115788574092696280331609123)
              ·
                refine ⟨173682861139044420497413685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115788574092696280331609123 173682861139044420497413685)
                ·
                  refine ⟨16282768231785414421632533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173682861139044420497413685 16282768231785414421632533)
                  ·
                    refine ⟨763254760864941301014025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16282768231785414421632533 763254760864941301014025)
                    ·
                      refine ⟨572441070648705975760519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763254760864941301014025 572441070648705975760519)
                      ·
                        rfl

theorem cell23_1114825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 6, 2].length) (baseStart_1114825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114825 prefixEnd_1114825 := by exact prefixLift 1114825
  have htrace : WordTrace (prefixWord ++ tailWord_1114825) baseStart_1114825 baseEnd_1114825 := by
    simpa [prefixWord, tailWord_1114825, baseEnd_1114825] using wordTrace_append hprefix tailTrace_1114825
  have hstable : (prefixWord ++ tailWord_1114825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114825).length < 2 ^ (prefixWord ++ tailWord_1114825).sum := by decide
  have hdescent : baseEnd_1114825 < baseStart_1114825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114842 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2]
def baseStart_1114842 : Nat := 118140960795 + 1114842 * 2 ^ 59
def prefixEnd_1114842 : Nat := 4983230072969 + 3 ^ 40 * 1114842 * 2
def baseEnd_1114842 : Nat := 572449799819832409247941

theorem tailTrace_1114842 : CollatzResearch.WordTrace tailWord_1114842 prefixEnd_1114842 572449799819832409247941 := by
  unfold tailWord_1114842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165407056781327175050695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27107752151416872466801853 10165407056781327175050695)
  ·
    refine ⟨15248110585171990762576043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10165407056781327175050695 15248110585171990762576043)
    ·
      refine ⟨22872165877757986143864065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15248110585171990762576043 22872165877757986143864065)
      ·
        refine ⟨17154124408318489607898049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22872165877757986143864065 17154124408318489607898049)
        ·
          refine ⟨12865593306238867205923537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17154124408318489607898049 12865593306238867205923537)
          ·
            refine ⟨9649194979679150404442653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12865593306238867205923537 9649194979679150404442653)
            ·
              refine ⟨3618448117379681401665995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9649194979679150404442653 3618448117379681401665995)
              ·
                refine ⟨5427672176069522102498993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618448117379681401665995 5427672176069522102498993)
                ·
                  refine ⟨4070754132052141576874245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5427672176069522102498993 4070754132052141576874245)
                  ·
                    refine ⟨763266399759776545663921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4070754132052141576874245 763266399759776545663921)
                    ·
                      refine ⟨572449799819832409247941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763266399759776545663921 572449799819832409247941)
                      ·
                        rfl

theorem cell23_1114842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_1114842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114842 prefixEnd_1114842 := by exact prefixLift 1114842
  have htrace : WordTrace (prefixWord ++ tailWord_1114842) baseStart_1114842 baseEnd_1114842 := by
    simpa [prefixWord, tailWord_1114842, baseEnd_1114842] using wordTrace_append hprefix tailTrace_1114842
  have hstable : (prefixWord ++ tailWord_1114842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114842).length < 2 ^ (prefixWord ++ tailWord_1114842).sum := by decide
  have hdescent : baseEnd_1114842 < baseStart_1114842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114848 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 10]
def baseStart_1114848 : Nat := 118140960795 + 1114848 * 2 ^ 59
def prefixEnd_1114848 : Nat := 4983230072969 + 3 ^ 40 * 1114848 * 2
def baseEnd_1114848 : Nat := 63605875633751042863657

theorem tailTrace_1114848 : CollatzResearch.WordTrace tailWord_1114848 prefixEnd_1114848 63605875633751042863657 := by
  unfold tailWord_1114848
  simp only [CollatzResearch.WordTrace]
  refine ⟨20330923532551785862460599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27107898043402381149947465 20330923532551785862460599)
  ·
    refine ⟨30496385298827678793690899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20330923532551785862460599 30496385298827678793690899)
    ·
      refine ⟨45744577948241518190536349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30496385298827678793690899 45744577948241518190536349)
      ·
        refine ⟨17154216730590569321451131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45744577948241518190536349 17154216730590569321451131)
        ·
          refine ⟨25731325095885853982176697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17154216730590569321451131 25731325095885853982176697)
          ·
            refine ⟨19298493821914390486632523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25731325095885853982176697 19298493821914390486632523)
            ·
              refine ⟨28947740732871585729948785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19298493821914390486632523 28947740732871585729948785)
              ·
                refine ⟨21710805549653689297461589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28947740732871585729948785 21710805549653689297461589)
                ·
                  refine ⟨63605875633751042863657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 21710805549653689297461589 63605875633751042863657)
                  ·
                    rfl

theorem cell23_1114848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 10].length) (baseStart_1114848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114848 prefixEnd_1114848 := by exact prefixLift 1114848
  have htrace : WordTrace (prefixWord ++ tailWord_1114848) baseStart_1114848 baseEnd_1114848 := by
    simpa [prefixWord, tailWord_1114848, baseEnd_1114848] using wordTrace_append hprefix tailTrace_1114848
  have hstable : (prefixWord ++ tailWord_1114848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114848).length < 2 ^ (prefixWord ++ tailWord_1114848).sum := by decide
  have hdescent : baseEnd_1114848 < baseStart_1114848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114852 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_1114852 : Nat := 118140960795 + 1114852 * 2 ^ 59
def prefixEnd_1114852 : Nat := 4983230072969 + 3 ^ 40 * 1114852 * 2
def baseEnd_1114852 : Nat := 190818311542125790040965

theorem tailTrace_1114852 : CollatzResearch.WordTrace tailWord_1114852 prefixEnd_1114852 190818311542125790040965 := by
  unfold tailWord_1114852
  simp only [CollatzResearch.WordTrace]
  refine ⟨20330996478544540204033405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27107995304726053605377873 20330996478544540204033405)
  ·
    refine ⟨7624123679454202576512527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20330996478544540204033405 7624123679454202576512527)
    ·
      refine ⟨11436185519181303864768791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7624123679454202576512527 11436185519181303864768791)
      ·
        refine ⟨17154278278771955797153187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11436185519181303864768791 17154278278771955797153187)
        ·
          refine ⟨25731417418157933695729781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17154278278771955797153187 25731417418157933695729781)
          ·
            refine ⟨2412320382952306283974667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25731417418157933695729781 2412320382952306283974667)
            ·
              refine ⟨3618480574428459425962001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412320382952306283974667 3618480574428459425962001)
              ·
                refine ⟨2713860430821344569471501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618480574428459425962001 2713860430821344569471501)
                ·
                  refine ⟨1017697661558004213551813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2713860430821344569471501 1017697661558004213551813)
                  ·
                    refine ⟨190818311542125790040965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1017697661558004213551813 190818311542125790040965)
                    ·
                      rfl

theorem cell23_1114852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_1114852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114852 prefixEnd_1114852 := by exact prefixLift 1114852
  have htrace : WordTrace (prefixWord ++ tailWord_1114852) baseStart_1114852 baseEnd_1114852 := by
    simpa [prefixWord, tailWord_1114852, baseEnd_1114852] using wordTrace_append hprefix tailTrace_1114852
  have hstable : (prefixWord ++ tailWord_1114852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114852).length < 2 ^ (prefixWord ++ tailWord_1114852).sum := by decide
  have hdescent : baseEnd_1114852 < baseStart_1114852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114862 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1114862 : Nat := 118140960795 + 1114862 * 2 ^ 59
def prefixEnd_1114862 : Nat := 4983230072969 + 3 ^ 40 * 1114862 * 2
def baseEnd_1114862 : Nat := 572460069432922330997849

theorem tailTrace_1114862 : CollatzResearch.WordTrace tailWord_1114862 prefixEnd_1114862 572460069432922330997849 := by
  unfold tailWord_1114862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082794710881606514491355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27108238458035234743953893 5082794710881606514491355)
  ·
    refine ⟨7624192066322409771737033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5082794710881606514491355 7624192066322409771737033)
    ·
      refine ⟨5718144049741807328802775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7624192066322409771737033 5718144049741807328802775)
      ·
        refine ⟨8577216074612710993204163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5718144049741807328802775 8577216074612710993204163)
        ·
          refine ⟨12865824111919066489806245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8577216074612710993204163 12865824111919066489806245)
          ·
            refine ⟨2412342020984824966838671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12865824111919066489806245 2412342020984824966838671)
            ·
              refine ⟨3618513031477237450258007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412342020984824966838671 3618513031477237450258007)
              ·
                refine ⟨5427769547215856175387011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618513031477237450258007 5427769547215856175387011)
                ·
                  refine ⟨8141654320823784263080517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427769547215856175387011 8141654320823784263080517)
                  ·
                    refine ⟨1526560185154459549327597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8141654320823784263080517 1526560185154459549327597)
                    ·
                      refine ⟨572460069432922330997849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526560185154459549327597 572460069432922330997849)
                      ·
                        rfl

theorem cell23_1114862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1114862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114862 prefixEnd_1114862 := by exact prefixLift 1114862
  have htrace : WordTrace (prefixWord ++ tailWord_1114862) baseStart_1114862 baseEnd_1114862 := by
    simpa [prefixWord, tailWord_1114862, baseEnd_1114862] using wordTrace_append hprefix tailTrace_1114862
  have hstable : (prefixWord ++ tailWord_1114862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114862).length < 2 ^ (prefixWord ++ tailWord_1114862).sum := by decide
  have hdescent : baseEnd_1114862 < baseStart_1114862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114882 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1114882 : Nat := 118140960795 + 1114882 * 2 ^ 59
def prefixEnd_1114882 : Nat := 4983230072969 + 3 ^ 40 * 1114882 * 2
def baseEnd_1114882 : Nat := 63607815449556916971973

theorem tailTrace_1114882 : CollatzResearch.WordTrace tailWord_1114882 prefixEnd_1114882 63607815449556916971973 := by
  unfold tailWord_1114882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165771786745098882914725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27108724764653597021105933 10165771786745098882914725)
  ·
    refine ⟨1906082210014706040546511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10165771786745098882914725 1906082210014706040546511)
    ·
      refine ⟨2859123315022059060819767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1906082210014706040546511 2859123315022059060819767)
      ·
        refine ⟨4288684972533088591229651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2859123315022059060819767 4288684972533088591229651)
        ·
          refine ⟨6433027458799632886844477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4288684972533088591229651 6433027458799632886844477)
          ·
            refine ⟨2412385297049862332566679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6433027458799632886844477 2412385297049862332566679)
            ·
              refine ⟨3618577945574793498850019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412385297049862332566679 3618577945574793498850019)
              ·
                refine ⟨5427866918362190248275029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618577945574793498850019 5427866918362190248275029)
                ·
                  refine ⟨63607815449556916971973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5427866918362190248275029 63607815449556916971973)
                  ·
                    rfl

theorem cell23_1114882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1114882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114882 prefixEnd_1114882 := by exact prefixLift 1114882
  have htrace : WordTrace (prefixWord ++ tailWord_1114882) baseStart_1114882 baseEnd_1114882 := by
    simpa [prefixWord, tailWord_1114882, baseEnd_1114882] using wordTrace_append hprefix tailTrace_1114882
  have hstable : (prefixWord ++ tailWord_1114882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114882).length < 2 ^ (prefixWord ++ tailWord_1114882).sum := by decide
  have hdescent : baseEnd_1114882 < baseStart_1114882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114912 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 1, 5]
def baseStart_1114912 : Nat := 118140960795 + 1114912 * 2 ^ 59
def prefixEnd_1114912 : Nat := 4983230072969 + 3 ^ 40 * 1114912 * 2
def baseEnd_1114912 : Nat := 190828581155215711790873

theorem tailTrace_1114912 : CollatzResearch.WordTrace tailWord_1114912 prefixEnd_1114912 190828581155215711790873 := by
  unfold tailWord_1114912
  simp only [CollatzResearch.WordTrace]
  refine ⟨20332090668435855327625495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27109454224581140436833993 20332090668435855327625495)
  ·
    refine ⟨30498136002653782991438243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20332090668435855327625495 30498136002653782991438243)
    ·
      refine ⟨45747204003980674487157365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30498136002653782991438243 45747204003980674487157365)
      ·
        refine ⟨4288800375373188233171003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45747204003980674487157365 4288800375373188233171003)
        ·
          refine ⟨6433200563059782349756505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4288800375373188233171003 6433200563059782349756505)
          ·
            refine ⟨4824900422294836762317379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6433200563059782349756505 4824900422294836762317379)
            ·
              refine ⟨7237350633442255143476069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4824900422294836762317379 7237350633442255143476069)
              ·
                refine ⟨1357003243770422839401763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7237350633442255143476069 1357003243770422839401763)
                ·
                  refine ⟨2035504865655634259102645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357003243770422839401763 2035504865655634259102645)
                  ·
                    refine ⟨190828581155215711790873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2035504865655634259102645 190828581155215711790873)
                    ·
                      rfl

theorem cell23_1114912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_1114912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114912 prefixEnd_1114912 := by exact prefixLift 1114912
  have htrace : WordTrace (prefixWord ++ tailWord_1114912) baseStart_1114912 baseEnd_1114912 := by
    simpa [prefixWord, tailWord_1114912, baseEnd_1114912] using wordTrace_append hprefix tailTrace_1114912
  have hstable : (prefixWord ++ tailWord_1114912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114912).length < 2 ^ (prefixWord ++ tailWord_1114912).sum := by decide
  have hdescent : baseEnd_1114912 < baseStart_1114912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114943 : List Nat := [1, 1, 2, 2, 5, 2, 3, 2, 1, 1, 3]
def baseStart_1114943 : Nat := 118140960795 + 1114943 * 2 ^ 59
def prefixEnd_1114943 : Nat := 4983230072969 + 3 ^ 40 * 1114943 * 2
def baseEnd_1114943 : Nat := 572501661365936514084977

theorem tailTrace_1114943 : CollatzResearch.WordTrace tailWord_1114943 prefixEnd_1114943 572501661365936514084977 := by
  unfold tailWord_1114943
  simp only [CollatzResearch.WordTrace]
  refine ⟨40665311999759402949629483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27110207999839601966419655 40665311999759402949629483)
  ·
    refine ⟨60997967999639104424444225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40665311999759402949629483 60997967999639104424444225)
    ·
      refine ⟨45748475999729328318333169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60997967999639104424444225 45748475999729328318333169)
      ·
        refine ⟨34311356999796996238749877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45748475999729328318333169 34311356999796996238749877)
        ·
          refine ⟨3216689718730968397382801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34311356999796996238749877 3216689718730968397382801)
          ·
            refine ⟨2412517289048226298037101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3216689718730968397382801 2412517289048226298037101)
            ·
              refine ⟨904693983393084861763913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2412517289048226298037101 904693983393084861763913)
              ·
                refine ⟨678520487544813646322935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904693983393084861763913 678520487544813646322935)
                ·
                  refine ⟨1017780731317220469484403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678520487544813646322935 1017780731317220469484403)
                  ·
                    refine ⟨1526671096975830704226605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1017780731317220469484403 1526671096975830704226605)
                    ·
                      refine ⟨572501661365936514084977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526671096975830704226605 572501661365936514084977)
                      ·
                        rfl

theorem cell23_1114943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_1114943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114943 prefixEnd_1114943 := by exact prefixLift 1114943
  have htrace : WordTrace (prefixWord ++ tailWord_1114943) baseStart_1114943 baseEnd_1114943 := by
    simpa [prefixWord, tailWord_1114943, baseEnd_1114943] using wordTrace_append hprefix tailTrace_1114943
  have hstable : (prefixWord ++ tailWord_1114943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114943).length < 2 ^ (prefixWord ++ tailWord_1114943).sum := by decide
  have hdescent : baseEnd_1114943 < baseStart_1114943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114949 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 3, 2, 2]
def baseStart_1114949 : Nat := 118140960795 + 1114949 * 2 ^ 59
def prefixEnd_1114949 : Nat := 4983230072969 + 3 ^ 40 * 1114949 * 2
def baseEnd_1114949 : Nat := 572504742249863490609949

theorem tailTrace_1114949 : CollatzResearch.WordTrace tailWord_1114949 prefixEnd_1114949 572504742249863490609949 := by
  unfold tailWord_1114949
  simp only [CollatzResearch.WordTrace]
  refine ⟨40665530837737665974347901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27110353891825110649565267 40665530837737665974347901)
  ·
    refine ⟨15249574064151624740380463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40665530837737665974347901 15249574064151624740380463)
    ·
      refine ⟨22874361096227437110570695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15249574064151624740380463 22874361096227437110570695)
      ·
        refine ⟨34311541644341155665856043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22874361096227437110570695 34311541644341155665856043)
        ·
          refine ⟨51467312466511733498784065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34311541644341155665856043 51467312466511733498784065)
          ·
            refine ⟨38600484349883800124088049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51467312466511733498784065 38600484349883800124088049)
            ·
              refine ⟨28950363262412850093066037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38600484349883800124088049 28950363262412850093066037)
              ·
                refine ⟨2714096555851204696224941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28950363262412850093066037 2714096555851204696224941)
                ·
                  refine ⟨1017786208444201761084353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2714096555851204696224941 1017786208444201761084353)
                  ·
                    refine ⟨763339656333151320813265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1017786208444201761084353 763339656333151320813265)
                    ·
                      refine ⟨572504742249863490609949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763339656333151320813265 572504742249863490609949)
                      ·
                        rfl

theorem cell23_1114949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_1114949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114949 prefixEnd_1114949 := by exact prefixLift 1114949
  have htrace : WordTrace (prefixWord ++ tailWord_1114949) baseStart_1114949 baseEnd_1114949 := by
    simpa [prefixWord, tailWord_1114949, baseEnd_1114949] using wordTrace_append hprefix tailTrace_1114949
  have hstable : (prefixWord ++ tailWord_1114949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114949).length < 2 ^ (prefixWord ++ tailWord_1114949).sum := by decide
  have hdescent : baseEnd_1114949 < baseStart_1114949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114950 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1114950 : Nat := 118140960795 + 1114950 * 2 ^ 59
def prefixEnd_1114950 : Nat := 4983230072969 + 3 ^ 40 * 1114950 * 2
def baseEnd_1114950 : Nat := 63611695081168665188605

theorem tailTrace_1114950 : CollatzResearch.WordTrace tailWord_1114950 prefixEnd_1114950 63611695081168665188605 := by
  unfold tailWord_1114950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270798978460438848285447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27110378207156028763422869 1270798978460438848285447)
  ·
    refine ⟨1906198467690658272428171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1270798978460438848285447 1906198467690658272428171)
    ·
      refine ⟨2859297701535987408642257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1906198467690658272428171 2859297701535987408642257)
      ·
        refine ⟨2144473276151990556481693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2859297701535987408642257 2144473276151990556481693)
        ·
          refine ⟨804177478556996458680635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2144473276151990556481693 804177478556996458680635)
          ·
            refine ⟨1206266217835494688020953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804177478556996458680635 1206266217835494688020953)
            ·
              refine ⟨904699663376621016015715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206266217835494688020953 904699663376621016015715)
              ·
                refine ⟨1357049495064931524023573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904699663376621016015715 1357049495064931524023573)
                ·
                  refine ⟨63611695081168665188605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1357049495064931524023573 63611695081168665188605)
                  ·
                    rfl

theorem cell23_1114950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1114950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114950 prefixEnd_1114950 := by exact prefixLift 1114950
  have htrace : WordTrace (prefixWord ++ tailWord_1114950) baseStart_1114950 baseEnd_1114950 := by
    simpa [prefixWord, tailWord_1114950, baseEnd_1114950] using wordTrace_append hprefix tailTrace_1114950
  have hstable : (prefixWord ++ tailWord_1114950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114950).length < 2 ^ (prefixWord ++ tailWord_1114950).sum := by decide
  have hdescent : baseEnd_1114950 < baseStart_1114950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114952 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_1114952 : Nat := 118140960795 + 1114952 * 2 ^ 59
def prefixEnd_1114952 : Nat := 4983230072969 + 3 ^ 40 * 1114952 * 2
def baseEnd_1114952 : Nat := 572506282691826978872435

theorem tailTrace_1114952 : CollatzResearch.WordTrace tailWord_1114952 prefixEnd_1114952 572506282691826978872435 := by
  unfold tailWord_1114952
  simp only [CollatzResearch.WordTrace]
  refine ⟨20332820128363398743353555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27110426837817864991138073 20332820128363398743353555)
  ·
    refine ⟨30499230192545098115030333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20332820128363398743353555 30499230192545098115030333)
    ·
      refine ⟨11437211322204411793136375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30499230192545098115030333 11437211322204411793136375)
      ·
        refine ⟨17155816983306617689704563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11437211322204411793136375 17155816983306617689704563)
        ·
          refine ⟨25733725474959926534556845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17155816983306617689704563 25733725474959926534556845)
          ·
            refine ⟨9650147053109972450458817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25733725474959926534556845 9650147053109972450458817)
            ·
              refine ⟨7237610289832479337844113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9650147053109972450458817 7237610289832479337844113)
              ·
                refine ⟨5428207717374359503383085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7237610289832479337844113 5428207717374359503383085)
                ·
                  refine ⟨2035577894015384813768657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5428207717374359503383085 2035577894015384813768657)
                  ·
                    refine ⟨1526683420511538610326493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2035577894015384813768657 1526683420511538610326493)
                    ·
                      refine ⟨572506282691826978872435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526683420511538610326493 572506282691826978872435)
                      ·
                        rfl

theorem cell23_1114952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_1114952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114952 prefixEnd_1114952 := by exact prefixLift 1114952
  have htrace : WordTrace (prefixWord ++ tailWord_1114952) baseStart_1114952 baseEnd_1114952 := by
    simpa [prefixWord, tailWord_1114952, baseEnd_1114952] using wordTrace_append hprefix tailTrace_1114952
  have hstable : (prefixWord ++ tailWord_1114952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114952).length < 2 ^ (prefixWord ++ tailWord_1114952).sum := by decide
  have hdescent : baseEnd_1114952 < baseStart_1114952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114962 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_1114962 : Nat := 118140960795 + 1114962 * 2 ^ 59
def prefixEnd_1114962 : Nat := 4983230072969 + 3 ^ 40 * 1114962 * 2
def baseEnd_1114962 : Nat := 572511417498371939747389

theorem tailTrace_1114962 : CollatzResearch.WordTrace tailWord_1114962 prefixEnd_1114962 572511417498371939747389 := by
  unfold tailWord_1114962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10166501246672642298642785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27110669991127046129714093 10166501246672642298642785)
  ·
    refine ⟨7624875935004481723982089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10166501246672642298642785 7624875935004481723982089)
    ·
      refine ⟨5718656951253361292986567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7624875935004481723982089 5718656951253361292986567)
      ·
        refine ⟨8577985426880041939479851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5718656951253361292986567 8577985426880041939479851)
        ·
          refine ⟨12866978140320062909219777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8577985426880041939479851 12866978140320062909219777)
          ·
            refine ⟨9650233605240047181914833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12866978140320062909219777 9650233605240047181914833)
            ·
              refine ⟨7237675203930035386436125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9650233605240047181914833 7237675203930035386436125)
              ·
                refine ⟨2714128201473763269913547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7237675203930035386436125 2714128201473763269913547)
                ·
                  refine ⟨4071192302210644904870321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714128201473763269913547 4071192302210644904870321)
                  ·
                    refine ⟨3053394226657983678652741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4071192302210644904870321 3053394226657983678652741)
                    ·
                      refine ⟨572511417498371939747389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3053394226657983678652741 572511417498371939747389)
                      ·
                        rfl

theorem cell23_1114962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_1114962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114962 prefixEnd_1114962 := by exact prefixLift 1114962
  have htrace : WordTrace (prefixWord ++ tailWord_1114962) baseStart_1114962 baseEnd_1114962 := by
    simpa [prefixWord, tailWord_1114962, baseEnd_1114962] using wordTrace_append hprefix tailTrace_1114962
  have hstable : (prefixWord ++ tailWord_1114962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114962).length < 2 ^ (prefixWord ++ tailWord_1114962).sum := by decide
  have hdescent : baseEnd_1114962 < baseStart_1114962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114969 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 3]
def baseStart_1114969 : Nat := 118140960795 + 1114969 * 2 ^ 59
def prefixEnd_1114969 : Nat := 4983230072969 + 3 ^ 40 * 1114969 * 2
def baseEnd_1114969 : Nat := 572515011862953412359857

theorem tailTrace_1114969 : CollatzResearch.WordTrace tailWord_1114969 prefixEnd_1114969 572515011862953412359857 := by
  unfold tailWord_1114969
  simp only [CollatzResearch.WordTrace]
  refine ⟨40666260297665209390075961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27110840198443472926717307 40666260297665209390075961)
  ·
    refine ⟨30499695223248907042556971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40666260297665209390075961 30499695223248907042556971)
    ·
      refine ⟨45749542834873360563835457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30499695223248907042556971 45749542834873360563835457)
      ·
        refine ⟨34312157126155020422876593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45749542834873360563835457 34312157126155020422876593)
        ·
          refine ⟨25734117844616265317157445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34312157126155020422876593 25734117844616265317157445)
          ·
            refine ⟨4825147095865549746967021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25734117844616265317157445 4825147095865549746967021)
            ·
              refine ⟨1809430160949581155112633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4825147095865549746967021 1809430160949581155112633)
              ·
                refine ⟨1357072620712185866334475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1809430160949581155112633 1357072620712185866334475)
                ·
                  refine ⟨2035608931068278799501713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357072620712185866334475 2035608931068278799501713)
                  ·
                    refine ⟨1526706698301209099626285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2035608931068278799501713 1526706698301209099626285)
                    ·
                      refine ⟨572515011862953412359857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526706698301209099626285 572515011862953412359857)
                      ·
                        rfl

theorem cell23_1114969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_1114969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114969 prefixEnd_1114969 := by exact prefixLift 1114969
  have htrace : WordTrace (prefixWord ++ tailWord_1114969) baseStart_1114969 baseEnd_1114969 := by
    simpa [prefixWord, tailWord_1114969, baseEnd_1114969] using wordTrace_append hprefix tailTrace_1114969
  have hstable : (prefixWord ++ tailWord_1114969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114969).length < 2 ^ (prefixWord ++ tailWord_1114969).sum := by decide
  have hdescent : baseEnd_1114969 < baseStart_1114969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114972 : List Nat := [2, 2, 4, 2, 1, 1, 2, 9]
def baseStart_1114972 : Nat := 118140960795 + 1114972 * 2 ^ 59
def prefixEnd_1114972 : Nat := 4983230072969 + 3 ^ 40 * 1114972 * 2
def baseEnd_1114972 : Nat := 21204316752033959282309

theorem tailTrace_1114972 : CollatzResearch.WordTrace tailWord_1114972 prefixEnd_1114972 21204316752033959282309 := by
  unfold tailWord_1114972
  simp only [CollatzResearch.WordTrace]
  refine ⟨20333184858327170451217585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27110913144436227268290113 20333184858327170451217585)
  ·
    refine ⟨15249888643745377838413189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20333184858327170451217585 15249888643745377838413189)
    ·
      refine ⟨2859354120702258344702473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15249888643745377838413189 2859354120702258344702473)
      ·
        refine ⟨2144515590526693758526855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2859354120702258344702473 2144515590526693758526855)
        ·
          refine ⟨3216773385790040637790283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144515590526693758526855 3216773385790040637790283)
          ·
            refine ⟨4825160078685060956685425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216773385790040637790283 4825160078685060956685425)
            ·
              refine ⟨3618870059013795717514069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825160078685060956685425 3618870059013795717514069)
              ·
                refine ⟨21204316752033959282309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3618870059013795717514069 21204316752033959282309)
                ·
                  rfl

theorem cell23_1114972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 9].length) (baseStart_1114972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114972 prefixEnd_1114972 := by exact prefixLift 1114972
  have htrace : WordTrace (prefixWord ++ tailWord_1114972) baseStart_1114972 baseEnd_1114972 := by
    simpa [prefixWord, tailWord_1114972, baseEnd_1114972] using wordTrace_append hprefix tailTrace_1114972
  have hstable : (prefixWord ++ tailWord_1114972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114972).length < 2 ^ (prefixWord ++ tailWord_1114972).sum := by decide
  have hdescent : baseEnd_1114972 < baseStart_1114972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114995 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 5]
def baseStart_1114995 : Nat := 118140960795 + 1114995 * 2 ^ 59
def prefixEnd_1114995 : Nat := 4983230072969 + 3 ^ 40 * 1114995 * 2
def baseEnd_1114995 : Nat := 572528362359970310634737

theorem tailTrace_1114995 : CollatzResearch.WordTrace tailWord_1114995 prefixEnd_1114995 572528362359970310634737 := by
  unfold tailWord_1114995
  simp only [CollatzResearch.WordTrace]
  refine ⟨40667208595571015830522439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27111472397047343887014959 40667208595571015830522439)
  ·
    refine ⟨61000812893356523745783659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40667208595571015830522439 61000812893356523745783659)
    ·
      refine ⟨91501219340034785618675489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61000812893356523745783659 91501219340034785618675489)
      ·
        refine ⟨68625914505026089214006617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91501219340034785618675489 68625914505026089214006617)
        ·
          refine ⟨51469435878769566910504963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68625914505026089214006617 51469435878769566910504963)
          ·
            refine ⟨77204153818154350365757445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51469435878769566910504963 77204153818154350365757445)
            ·
              refine ⟨14475778840903940693579521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77204153818154350365757445 14475778840903940693579521)
              ·
                refine ⟨10856834130677955520184641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14475778840903940693579521 10856834130677955520184641)
                ·
                  refine ⟨8142625598008466640138481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10856834130677955520184641 8142625598008466640138481)
                  ·
                    refine ⟨6106969198506349980103861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8142625598008466640138481 6106969198506349980103861)
                    ·
                      refine ⟨572528362359970310634737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6106969198506349980103861 572528362359970310634737)
                      ·
                        rfl

theorem cell23_1114995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_1114995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1114995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1114995 prefixEnd_1114995 := by exact prefixLift 1114995
  have htrace : WordTrace (prefixWord ++ tailWord_1114995) baseStart_1114995 baseEnd_1114995 := by
    simpa [prefixWord, tailWord_1114995, baseEnd_1114995] using wordTrace_append hprefix tailTrace_1114995
  have hstable : (prefixWord ++ tailWord_1114995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114995).length < 2 ^ (prefixWord ++ tailWord_1114995).sum := by decide
  have hdescent : baseEnd_1114995 < baseStart_1114995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115006 : List Nat := [4, 2, 3, 1, 2, 2, 1, 8]
def baseStart_1115006 : Nat := 118140960795 + 1115006 * 2 ^ 59
def prefixEnd_1115006 : Nat := 4983230072969 + 3 ^ 40 * 1115006 * 2
def baseEnd_1115006 : Nat := 21204963357302583985081

theorem tailTrace_1115006 : CollatzResearch.WordTrace tailWord_1115006 prefixEnd_1115006 21204963357302583985081 := by
  unfold tailWord_1115006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083451224816395588646609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27111739865687443139448581 5083451224816395588646609)
  ·
    refine ⟨3812588418612296691484957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5083451224816395588646609 3812588418612296691484957)
    ·
      refine ⟨1429720656979611259306859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3812588418612296691484957 1429720656979611259306859)
      ·
        refine ⟨2144580985469416888960289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429720656979611259306859 2144580985469416888960289)
        ·
          refine ⟨1608435739102062666720217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2144580985469416888960289 1608435739102062666720217)
          ·
            refine ⟨1206326804326547000040163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1608435739102062666720217 1206326804326547000040163)
            ·
              refine ⟨1809490206489820500060245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206326804326547000040163 1809490206489820500060245)
              ·
                refine ⟨21204963357302583985081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1809490206489820500060245 21204963357302583985081)
                ·
                  rfl

theorem cell23_1115006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_1115006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115006 prefixEnd_1115006 := by exact prefixLift 1115006
  have htrace : WordTrace (prefixWord ++ tailWord_1115006) baseStart_1115006 baseEnd_1115006 := by
    simpa [prefixWord, tailWord_1115006, baseEnd_1115006] using wordTrace_append hprefix tailTrace_1115006
  have hstable : (prefixWord ++ tailWord_1115006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115006).length < 2 ^ (prefixWord ++ tailWord_1115006).sum := by decide
  have hdescent : baseEnd_1115006 < baseStart_1115006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115016 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_1115016 : Nat := 118140960795 + 1115016 * 2 ^ 59
def prefixEnd_1115016 : Nat := 4983230072969 + 3 ^ 40 * 1115016 * 2
def baseEnd_1115016 : Nat := 572539145453714728472141

theorem tailTrace_1115016 : CollatzResearch.WordTrace tailWord_1115016 prefixEnd_1115016 572539145453714728472141 := by
  unfold tailWord_1115016
  simp only [CollatzResearch.WordTrace]
  refine ⟨20333987264247468208518451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27111983018996624278024601 20333987264247468208518451)
  ·
    refine ⟨30500980896371202312777677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20333987264247468208518451 30500980896371202312777677)
    ·
      refine ⟨11437867836139200867291629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30500980896371202312777677 11437867836139200867291629)
      ·
        refine ⟨4289200438552200325234361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11437867836139200867291629 4289200438552200325234361)
        ·
          refine ⟨3216900328914150243925771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4289200438552200325234361 3216900328914150243925771)
          ·
            refine ⟨4825350493371225365888657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216900328914150243925771 4825350493371225365888657)
            ·
              refine ⟨3619012870028419024416493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825350493371225365888657 3619012870028419024416493)
              ·
                refine ⟨1357129826260657134156185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3619012870028419024416493 1357129826260657134156185)
                ·
                  refine ⟨1017847369695492850617139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1357129826260657134156185 1017847369695492850617139)
                  ·
                    refine ⟨1526771054543239275925709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1017847369695492850617139 1526771054543239275925709)
                    ·
                      refine ⟨572539145453714728472141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1526771054543239275925709 572539145453714728472141)
                      ·
                        rfl

theorem cell23_1115016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_1115016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115016 prefixEnd_1115016 := by exact prefixLift 1115016
  have htrace : WordTrace (prefixWord ++ tailWord_1115016) baseStart_1115016 baseEnd_1115016 := by
    simpa [prefixWord, tailWord_1115016, baseEnd_1115016] using wordTrace_append hprefix tailTrace_1115016
  have hstable : (prefixWord ++ tailWord_1115016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115016).length < 2 ^ (prefixWord ++ tailWord_1115016).sum := by decide
  have hdescent : baseEnd_1115016 < baseStart_1115016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115055 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_1115055 : Nat := 118140960795 + 1115055 * 2 ^ 59
def prefixEnd_1115055 : Nat := 4983230072969 + 3 ^ 40 * 1115055 * 2
def baseEnd_1115055 : Nat := 572559171199240075884461

theorem tailTrace_1115055 : CollatzResearch.WordTrace tailWord_1115055 prefixEnd_1115055 572559171199240075884461 := by
  unfold tailWord_1115055
  simp only [CollatzResearch.WordTrace]
  refine ⟨40669396975353646077706619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27112931316902430718471079 40669396975353646077706619)
  ·
    refine ⟨61004095463030469116559929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40669396975353646077706619 61004095463030469116559929)
    ·
      refine ⟨45753071597272851837419947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61004095463030469116559929 45753071597272851837419947)
      ·
        refine ⟨68629607395909277756129921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45753071597272851837419947 68629607395909277756129921)
        ·
          refine ⟨51472205546931958317097441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68629607395909277756129921 51472205546931958317097441)
          ·
            refine ⟨38604154160198968737823081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51472205546931958317097441 38604154160198968737823081)
            ·
              refine ⟨28953115620149226553367311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38604154160198968737823081 28953115620149226553367311)
              ·
                refine ⟨43429673430223839830050967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28953115620149226553367311 43429673430223839830050967)
                ·
                  refine ⟨65144510145335759745076451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43429673430223839830050967 65144510145335759745076451)
                  ·
                    refine ⟨97716765218003639617614677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65144510145335759745076451 97716765218003639617614677)
                    ·
                      refine ⟨572559171199240075884461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 97716765218003639617614677 572559171199240075884461)
                      ·
                        rfl

theorem cell23_1115055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_1115055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115055 prefixEnd_1115055 := by exact prefixLift 1115055
  have htrace : WordTrace (prefixWord ++ tailWord_1115055) baseStart_1115055 baseEnd_1115055 := by
    simpa [prefixWord, tailWord_1115055, baseEnd_1115055] using wordTrace_append hprefix tailTrace_1115055
  have hstable : (prefixWord ++ tailWord_1115055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115055).length < 2 ^ (prefixWord ++ tailWord_1115055).sum := by decide
  have hdescent : baseEnd_1115055 < baseStart_1115055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115096 : List Nat := [2, 1, 2, 2, 2, 5, 1, 3, 5]
def baseStart_1115096 : Nat := 118140960795 + 1115096 * 2 ^ 59
def prefixEnd_1115096 : Nat := 4983230072969 + 3 ^ 40 * 1115096 * 2
def baseEnd_1115096 : Nat := 63620024878452712830197

theorem tailTrace_1115096 : CollatzResearch.WordTrace tailWord_1115096 prefixEnd_1115096 63620024878452712830197 := by
  unfold tailWord_1115096
  simp only [CollatzResearch.WordTrace]
  refine ⟨20335446184102555039974571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27113928245470073386632761 20335446184102555039974571)
  ·
    refine ⟨30503169276153832559961857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20335446184102555039974571 30503169276153832559961857)
    ·
      refine ⟨22877376957115374419971393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30503169276153832559961857 22877376957115374419971393)
      ·
        refine ⟨17158032717836530814978545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22877376957115374419971393 17158032717836530814978545)
        ·
          refine ⟨12868524538377398111233909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17158032717836530814978545 12868524538377398111233909)
          ·
            refine ⟨1206424175472881072928179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12868524538377398111233909 1206424175472881072928179)
            ·
              refine ⟨1809636263209321609392269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206424175472881072928179 1809636263209321609392269)
              ·
                refine ⟨678613598703495603522101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1809636263209321609392269 678613598703495603522101)
                ·
                  refine ⟨63620024878452712830197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 678613598703495603522101 63620024878452712830197)
                  ·
                    rfl

theorem cell23_1115096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 5].length) (baseStart_1115096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115096 prefixEnd_1115096 := by exact prefixLift 1115096
  have htrace : WordTrace (prefixWord ++ tailWord_1115096) baseStart_1115096 baseEnd_1115096 := by
    simpa [prefixWord, tailWord_1115096, baseEnd_1115096] using wordTrace_append hprefix tailTrace_1115096
  have hstable : (prefixWord ++ tailWord_1115096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115096).length < 2 ^ (prefixWord ++ tailWord_1115096).sum := by decide
  have hdescent : baseEnd_1115096 < baseStart_1115096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115129 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 1, 6, 2]
def baseStart_1115129 : Nat := 118140960795 + 1115129 * 2 ^ 59
def prefixEnd_1115129 : Nat := 4983230072969 + 3 ^ 40 * 1115129 * 2
def baseEnd_1115129 : Nat := 572597168767672786359121

theorem tailTrace_1115129 : CollatzResearch.WordTrace tailWord_1115129 prefixEnd_1115129 572597168767672786359121 := by
  unfold tailWord_1115129
  simp only [CollatzResearch.WordTrace]
  refine ⟨40672095977085556715900441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27114730651390371143933627 40672095977085556715900441)
  ·
    refine ⟨30504071982814167536925331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40672095977085556715900441 30504071982814167536925331)
    ·
      refine ⟨45756107974221251305387997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30504071982814167536925331 45756107974221251305387997)
      ·
        refine ⟨17158540490332969239520499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45756107974221251305387997 17158540490332969239520499)
        ·
          refine ⟨25737810735499453859280749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17158540490332969239520499 25737810735499453859280749)
          ·
            refine ⟨9651679025812295197230281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25737810735499453859280749 9651679025812295197230281)
            ·
              refine ⟨7238759269359221397922711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9651679025812295197230281 7238759269359221397922711)
              ·
                refine ⟨10858138904038832096884067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238759269359221397922711 10858138904038832096884067)
                ·
                  refine ⟨16287208356058248145326101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10858138904038832096884067 16287208356058248145326101)
                  ·
                    refine ⟨763462891690230381812161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16287208356058248145326101 763462891690230381812161)
                    ·
                      refine ⟨572597168767672786359121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763462891690230381812161 572597168767672786359121)
                      ·
                        rfl

theorem cell23_1115129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_1115129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115129 prefixEnd_1115129 := by exact prefixLift 1115129
  have htrace : WordTrace (prefixWord ++ tailWord_1115129) baseStart_1115129 baseEnd_1115129 := by
    simpa [prefixWord, tailWord_1115129, baseEnd_1115129] using wordTrace_append hprefix tailTrace_1115129
  have hstable : (prefixWord ++ tailWord_1115129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115129).length < 2 ^ (prefixWord ++ tailWord_1115129).sum := by decide
  have hdescent : baseEnd_1115129 < baseStart_1115129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115146 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1115146 : Nat := 118140960795 + 1115146 * 2 ^ 59
def prefixEnd_1115146 : Nat := 4983230072969 + 3 ^ 40 * 1115146 * 2
def baseEnd_1115146 : Nat := 572605897938799219846543

theorem tailTrace_1115146 : CollatzResearch.WordTrace tailWord_1115146 prefixEnd_1115146 572605897938799219846543 := by
  unfold tailWord_1115146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168179004505992154817323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27115144012015979079512861 10168179004505992154817323)
  ·
    refine ⟨15252268506758988232225985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10168179004505992154817323 15252268506758988232225985)
    ·
      refine ⟨11439201380069241174169489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15252268506758988232225985 11439201380069241174169489)
      ·
        refine ⟨8579401035051930880627117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11439201380069241174169489 8579401035051930880627117)
        ·
          refine ⟨3217275388144474080235169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8579401035051930880627117 3217275388144474080235169)
          ·
            refine ⟨2412956541108355560176377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3217275388144474080235169 2412956541108355560176377)
            ·
              refine ⟨1809717405831266670132283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2412956541108355560176377 1809717405831266670132283)
              ·
                refine ⟨2714576108746900005198425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1809717405831266670132283 2714576108746900005198425)
                ·
                  refine ⟨2035932081560175003898819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2714576108746900005198425 2035932081560175003898819)
                  ·
                    refine ⟨3053898122340262505848229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2035932081560175003898819 3053898122340262505848229)
                    ·
                      refine ⟨572605897938799219846543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3053898122340262505848229 572605897938799219846543)
                      ·
                        rfl

theorem cell23_1115146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1115146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115146 prefixEnd_1115146 := by exact prefixLift 1115146
  have htrace : WordTrace (prefixWord ++ tailWord_1115146) baseStart_1115146 baseEnd_1115146 := by
    simpa [prefixWord, tailWord_1115146, baseEnd_1115146] using wordTrace_append hprefix tailTrace_1115146
  have hstable : (prefixWord ++ tailWord_1115146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115146).length < 2 ^ (prefixWord ++ tailWord_1115146).sum := by decide
  have hdescent : baseEnd_1115146 < baseStart_1115146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115169 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 6]
def baseStart_1115169 : Nat := 118140960795 + 1115169 * 2 ^ 59
def prefixEnd_1115169 : Nat := 4983230072969 + 3 ^ 40 * 1115169 * 2
def baseEnd_1115169 : Nat := 63624189777094736650993

theorem tailTrace_1115169 : CollatzResearch.WordTrace tailWord_1115169 prefixEnd_1115169 63624189777094736650993 := by
  unfold tailWord_1115169
  simp only [CollatzResearch.WordTrace]
  refine ⟨40673554896940643547356561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27115703264627095698237707 40673554896940643547356561)
  ·
    refine ⟨30505166172705482660517421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40673554896940643547356561 30505166172705482660517421)
    ·
      refine ⟨11439437314764555997694033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30505166172705482660517421 11439437314764555997694033)
      ·
        refine ⟨8579577986073416998270525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11439437314764555997694033 8579577986073416998270525)
        ·
          refine ⟨3217341744777531374351447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8579577986073416998270525 3217341744777531374351447)
          ·
            refine ⟨4826012617166297061527171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217341744777531374351447 4826012617166297061527171)
            ·
              refine ⟨7239018925749445592290757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4826012617166297061527171 7239018925749445592290757)
              ·
                refine ⟨1357316048578021048554517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7239018925749445592290757 1357316048578021048554517)
                ·
                  refine ⟨63624189777094736650993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1357316048578021048554517 63624189777094736650993)
                  ·
                    rfl

theorem cell23_1115169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 6].length) (baseStart_1115169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115169 prefixEnd_1115169 := by exact prefixLift 1115169
  have htrace : WordTrace (prefixWord ++ tailWord_1115169) baseStart_1115169 baseEnd_1115169 := by
    simpa [prefixWord, tailWord_1115169, baseEnd_1115169] using wordTrace_append hprefix tailTrace_1115169
  have hstable : (prefixWord ++ tailWord_1115169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115169).length < 2 ^ (prefixWord ++ tailWord_1115169).sum := by decide
  have hdescent : baseEnd_1115169 < baseStart_1115169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115196 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_1115196 : Nat := 118140960795 + 1115196 * 2 ^ 59
def prefixEnd_1115196 : Nat := 4983230072969 + 3 ^ 40 * 1115196 * 2
def baseEnd_1115196 : Nat := 572631571971524024221313

theorem tailTrace_1115196 : CollatzResearch.WordTrace tailWord_1115196 prefixEnd_1115196 572631571971524024221313 := by
  unfold tailWord_1115196
  simp only [CollatzResearch.WordTrace]
  refine ⟨20337269833921413579294721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27116359778561884772392961 20337269833921413579294721)
  ·
    refine ⟨15252952375441060184471041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20337269833921413579294721 15252952375441060184471041)
    ·
      refine ⟨11439714281580795138353281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15252952375441060184471041 11439714281580795138353281)
      ·
        refine ⟨8579785711185596353764961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11439714281580795138353281 8579785711185596353764961)
        ·
          refine ⟨6434839283389197265323721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8579785711185596353764961 6434839283389197265323721)
          ·
            refine ⟨4826129462541897948992791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6434839283389197265323721 4826129462541897948992791)
            ·
              refine ⟨7239194193812846923489187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4826129462541897948992791 7239194193812846923489187)
              ·
                refine ⟨10858791290719270385233781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7239194193812846923489187 10858791290719270385233781)
                ·
                  refine ⟨1018011683504931598615667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10858791290719270385233781 1018011683504931598615667)
                  ·
                    refine ⟨1527017525257397397923501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1018011683504931598615667 1527017525257397397923501)
                    ·
                      refine ⟨572631571971524024221313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1527017525257397397923501 572631571971524024221313)
                      ·
                        rfl

theorem cell23_1115196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_1115196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115196 prefixEnd_1115196 := by exact prefixLift 1115196
  have htrace : WordTrace (prefixWord ++ tailWord_1115196) baseStart_1115196 baseEnd_1115196 := by
    simpa [prefixWord, tailWord_1115196, baseEnd_1115196] using wordTrace_append hprefix tailTrace_1115196
  have hstable : (prefixWord ++ tailWord_1115196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115196).length < 2 ^ (prefixWord ++ tailWord_1115196).sum := by decide
  have hdescent : baseEnd_1115196 < baseStart_1115196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115199 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 1, 5]
def baseStart_1115199 : Nat := 118140960795 + 1115199 * 2 ^ 59
def prefixEnd_1115199 : Nat := 4983230072969 + 3 ^ 40 * 1115199 * 2
def baseEnd_1115199 : Nat := 190877704137829170827933

theorem tailTrace_1115199 : CollatzResearch.WordTrace tailWord_1115199 prefixEnd_1115199 190877704137829170827933 := by
  unfold tailWord_1115199
  simp only [CollatzResearch.WordTrace]
  refine ⟨40674649086831958670948651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27116432724554639113965767 40674649086831958670948651)
  ·
    refine ⟨61011973630247938006422977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40674649086831958670948651 61011973630247938006422977)
    ·
      refine ⟨45758980222685953504817233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61011973630247938006422977 45758980222685953504817233)
      ·
        refine ⟨34319235167014465128612925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45758980222685953504817233 34319235167014465128612925)
        ·
          refine ⟨12869713187630424423229847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34319235167014465128612925 12869713187630424423229847)
          ·
            refine ⟨19304569781445636634844771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12869713187630424423229847 19304569781445636634844771)
            ·
              refine ⟨28956854672168454952267157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19304569781445636634844771 28956854672168454952267157)
              ·
                refine ⟨1357352562757896325887523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28956854672168454952267157 1357352562757896325887523)
                ·
                  refine ⟨2036028844136844488831285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357352562757896325887523 2036028844136844488831285)
                  ·
                    refine ⟨190877704137829170827933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2036028844136844488831285 190877704137829170827933)
                    ·
                      rfl

theorem cell23_1115199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_1115199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115199 prefixEnd_1115199 := by exact prefixLift 1115199
  have htrace : WordTrace (prefixWord ++ tailWord_1115199) baseStart_1115199 baseEnd_1115199 := by
    simpa [prefixWord, tailWord_1115199, baseEnd_1115199] using wordTrace_append hprefix tailTrace_1115199
  have hstable : (prefixWord ++ tailWord_1115199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115199).length < 2 ^ (prefixWord ++ tailWord_1115199).sum := by decide
  have hdescent : baseEnd_1115199 < baseStart_1115199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115239 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1115239 : Nat := 118140960795 + 1115239 * 2 ^ 59
def prefixEnd_1115239 : Nat := 4983230072969 + 3 ^ 40 * 1115239 * 2
def baseEnd_1115239 : Nat := 572653651639667355983615

theorem tailTrace_1115239 : CollatzResearch.WordTrace tailWord_1115239 prefixEnd_1115239 572653651639667355983615 := by
  unfold tailWord_1115239
  simp only [CollatzResearch.WordTrace]
  refine ⟨40676108006687045502404771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27117405337791363668269847 40676108006687045502404771)
  ·
    refine ⟨61014162010030568253607157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40676108006687045502404771 61014162010030568253607157)
    ·
      refine ⟨5720077688440365773775671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61014162010030568253607157 5720077688440365773775671)
      ·
        refine ⟨8580116532660548660663507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720077688440365773775671 8580116532660548660663507)
        ·
          refine ⟨12870174798990822990995261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8580116532660548660663507 12870174798990822990995261)
          ·
            refine ⟨4826315549621558621623223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12870174798990822990995261 4826315549621558621623223)
            ·
              refine ⟨7239473324432337932434835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4826315549621558621623223 7239473324432337932434835)
              ·
                refine ⟨10859209986648506898652253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7239473324432337932434835 10859209986648506898652253)
                ·
                  refine ⟨4072203744993190086994595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10859209986648506898652253 4072203744993190086994595)
                  ·
                    refine ⟨6108305617489785130491893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4072203744993190086994595 6108305617489785130491893)
                    ·
                      refine ⟨572653651639667355983615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6108305617489785130491893 572653651639667355983615)
                      ·
                        rfl

theorem cell23_1115239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1115239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115239 prefixEnd_1115239 := by exact prefixLift 1115239
  have htrace : WordTrace (prefixWord ++ tailWord_1115239) baseStart_1115239 baseEnd_1115239 := by
    simpa [prefixWord, tailWord_1115239, baseEnd_1115239] using wordTrace_append hprefix tailTrace_1115239
  have hstable : (prefixWord ++ tailWord_1115239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115239).length < 2 ^ (prefixWord ++ tailWord_1115239).sum := by decide
  have hdescent : baseEnd_1115239 < baseStart_1115239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115246 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1115246 : Nat := 118140960795 + 1115246 * 2 ^ 59
def prefixEnd_1115246 : Nat := 4983230072969 + 3 ^ 40 * 1115246 * 2
def baseEnd_1115246 : Nat := 190885748668082942865361

theorem tailTrace_1115246 : CollatzResearch.WordTrace tailWord_1115246 prefixEnd_1115246 190885748668082942865361 := by
  unfold tailWord_1115246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5084545414707710712238699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27117575545107790465273061 5084545414707710712238699)
  ·
    refine ⟨7626818122061566068358049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5084545414707710712238699 7626818122061566068358049)
    ·
      refine ⟨5720113591546174551268537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7626818122061566068358049 5720113591546174551268537)
      ·
        refine ⟨4290085193659630913451403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5720113591546174551268537 4290085193659630913451403)
        ·
          refine ⟨6435127790489446370177105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4290085193659630913451403 6435127790489446370177105)
          ·
            refine ⟨4826345842867084777632829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6435127790489446370177105 4826345842867084777632829)
            ·
              refine ⟨1809879691075156791612311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4826345842867084777632829 1809879691075156791612311)
              ·
                refine ⟨2714819536612735187418467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1809879691075156791612311 2714819536612735187418467)
                ·
                  refine ⟨4072229304919102781127701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714819536612735187418467 4072229304919102781127701)
                  ·
                    refine ⟨190885748668082942865361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4072229304919102781127701 190885748668082942865361)
                    ·
                      rfl

theorem cell23_1115246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1115246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115246 prefixEnd_1115246 := by exact prefixLift 1115246
  have htrace : WordTrace (prefixWord ++ tailWord_1115246) baseStart_1115246 baseEnd_1115246 := by
    simpa [prefixWord, tailWord_1115246, baseEnd_1115246] using wordTrace_append hprefix tailTrace_1115246
  have hstable : (prefixWord ++ tailWord_1115246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115246).length < 2 ^ (prefixWord ++ tailWord_1115246).sum := by decide
  have hdescent : baseEnd_1115246 < baseStart_1115246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115249 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_1115249 : Nat := 118140960795 + 1115249 * 2 ^ 59
def prefixEnd_1115249 : Nat := 4983230072969 + 3 ^ 40 * 1115249 * 2
def baseEnd_1115249 : Nat := 572658786446212316858569

theorem tailTrace_1115249 : CollatzResearch.WordTrace tailWord_1115249 prefixEnd_1115249 572658786446212316858569 := by
  unfold tailWord_1115249
  simp only [CollatzResearch.WordTrace]
  refine ⟨40676472736650817210268801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27117648491100544806845867 40676472736650817210268801)
  ·
    refine ⟨30507354552488112907701601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40676472736650817210268801 30507354552488112907701601)
    ·
      refine ⟨22880515914366084680776201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30507354552488112907701601 22880515914366084680776201)
      ·
        refine ⟨17160386935774563510582151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22880515914366084680776201 17160386935774563510582151)
        ·
          refine ⟨25740580403661845265873227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17160386935774563510582151 25740580403661845265873227)
          ·
            refine ⟨38610870605492767898809841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25740580403661845265873227 38610870605492767898809841)
            ·
              refine ⟨28958152954119575924107381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38610870605492767898809841 28958152954119575924107381)
              ·
                refine ⟨2714826839448710242885067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28958152954119575924107381 2714826839448710242885067)
                ·
                  refine ⟨4072240259173065364327601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714826839448710242885067 4072240259173065364327601)
                  ·
                    refine ⟨3054180194379799023245701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4072240259173065364327601 3054180194379799023245701)
                    ·
                      refine ⟨572658786446212316858569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3054180194379799023245701 572658786446212316858569)
                      ·
                        rfl

theorem cell23_1115249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_1115249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115249 prefixEnd_1115249 := by exact prefixLift 1115249
  have htrace : WordTrace (prefixWord ++ tailWord_1115249) baseStart_1115249 baseEnd_1115249 := by
    simpa [prefixWord, tailWord_1115249, baseEnd_1115249] using wordTrace_append hprefix tailTrace_1115249
  have hstable : (prefixWord ++ tailWord_1115249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115249).length < 2 ^ (prefixWord ++ tailWord_1115249).sum := by decide
  have hdescent : baseEnd_1115249 < baseStart_1115249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115256 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_1115256 : Nat := 118140960795 + 1115256 * 2 ^ 59
def prefixEnd_1115256 : Nat := 4983230072969 + 3 ^ 40 * 1115256 * 2
def baseEnd_1115256 : Nat := 572662380810793789471037

theorem tailTrace_1115256 : CollatzResearch.WordTrace tailWord_1115256 prefixEnd_1115256 572662380810793789471037 := by
  unfold tailWord_1115256
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338364023812728702886811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27117818698416971603849081 20338364023812728702886811)
  ·
    refine ⟨30507546035719093054330217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20338364023812728702886811 30507546035719093054330217)
    ·
      refine ⟨22880659526789319790747663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30507546035719093054330217 22880659526789319790747663)
      ·
        refine ⟨34320989290183979686121495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22880659526789319790747663 34320989290183979686121495)
        ·
          refine ⟨51481483935275969529182243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34320989290183979686121495 51481483935275969529182243)
          ·
            refine ⟨77222225902913954293773365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51481483935275969529182243 77222225902913954293773365)
            ·
              refine ⟨7239583678398183215041253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77222225902913954293773365 7239583678398183215041253)
              ·
                refine ⟨1357421939699659352820235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7239583678398183215041253 1357421939699659352820235)
                ·
                  refine ⟨2036132909549489029230353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357421939699659352820235 2036132909549489029230353)
                  ·
                    refine ⟨1527099682162116771922765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2036132909549489029230353 1527099682162116771922765)
                    ·
                      refine ⟨572662380810793789471037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1527099682162116771922765 572662380810793789471037)
                      ·
                        rfl

theorem cell23_1115256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_1115256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115256 prefixEnd_1115256 := by exact prefixLift 1115256
  have htrace : WordTrace (prefixWord ++ tailWord_1115256) baseStart_1115256 baseEnd_1115256 := by
    simpa [prefixWord, tailWord_1115256, baseEnd_1115256] using wordTrace_append hprefix tailTrace_1115256
  have hstable : (prefixWord ++ tailWord_1115256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115256).length < 2 ^ (prefixWord ++ tailWord_1115256).sum := by decide
  have hdescent : baseEnd_1115256 < baseStart_1115256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115346 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1115346 : Nat := 118140960795 + 1115346 * 2 ^ 59
def prefixEnd_1115346 : Nat := 4983230072969 + 3 ^ 40 * 1115346 * 2
def baseEnd_1115346 : Nat := 572708594069698437345623

theorem tailTrace_1115346 : CollatzResearch.WordTrace tailWord_1115346 prefixEnd_1115346 572708594069698437345623 := by
  unfold tailWord_1115346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10170002654324850694137473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27120007078199601851033261 10170002654324850694137473)
  ·
    refine ⟨7627501990743638020603105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10170002654324850694137473 7627501990743638020603105)
    ·
      refine ⟨5720626493057728515452329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7627501990743638020603105 5720626493057728515452329)
      ·
        refine ⟨4290469869793296386589247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5720626493057728515452329 4290469869793296386589247)
        ·
          refine ⟨6435704804689944579883871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4290469869793296386589247 6435704804689944579883871)
          ·
            refine ⟨9653557207034916869825807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6435704804689944579883871 9653557207034916869825807)
            ·
              refine ⟨14480335810552375304738711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9653557207034916869825807 14480335810552375304738711)
              ·
                refine ⟨21720503715828562957108067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14480335810552375304738711 21720503715828562957108067)
                ·
                  refine ⟨32580755573742844435662101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21720503715828562957108067 32580755573742844435662101)
                  ·
                    refine ⟨1527222917519195832921661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32580755573742844435662101 1527222917519195832921661)
                    ·
                      refine ⟨572708594069698437345623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1527222917519195832921661 572708594069698437345623)
                      ·
                        rfl

theorem cell23_1115346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1115346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115346 prefixEnd_1115346 := by exact prefixLift 1115346
  have htrace : WordTrace (prefixWord ++ tailWord_1115346) baseStart_1115346 baseEnd_1115346 := by
    simpa [prefixWord, tailWord_1115346, baseEnd_1115346] using wordTrace_append hprefix tailTrace_1115346
  have hstable : (prefixWord ++ tailWord_1115346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115346).length < 2 ^ (prefixWord ++ tailWord_1115346).sum := by decide
  have hdescent : baseEnd_1115346 < baseStart_1115346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115360 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 2, 2, 2]
def baseStart_1115360 : Nat := 118140960795 + 1115360 * 2 ^ 59
def prefixEnd_1115360 : Nat := 4983230072969 + 3 ^ 40 * 1115360 * 2
def baseEnd_1115360 : Nat := 572715782798861382570559

theorem tailTrace_1115360 : CollatzResearch.WordTrace tailWord_1115360 prefixEnd_1115360 572715782798861382570559 := by
  unfold tailWord_1115360
  simp only [CollatzResearch.WordTrace]
  refine ⟨20340260619624341583779767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27120347492832455445039689 20340260619624341583779767)
  ·
    refine ⟨30510390929436512375669651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20340260619624341583779767 30510390929436512375669651)
    ·
      refine ⟨45765586394154768563504477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30510390929436512375669651 45765586394154768563504477)
      ·
        refine ⟨17162094897808038211314179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45765586394154768563504477 17162094897808038211314179)
        ·
          refine ⟨25743142346712057316971269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17162094897808038211314179 25743142346712057316971269)
          ·
            refine ⟨4826839190008510746932113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25743142346712057316971269 4826839190008510746932113)
            ·
              refine ⟨3620129392506383060199085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4826839190008510746932113 3620129392506383060199085)
              ·
                refine ⟨1357548522189893647574657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3620129392506383060199085 1357548522189893647574657)
                ·
                  refine ⟨1018161391642420235680993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1357548522189893647574657 1018161391642420235680993)
                  ·
                    refine ⟨763621043731815176760745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1018161391642420235680993 763621043731815176760745)
                    ·
                      refine ⟨572715782798861382570559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763621043731815176760745 572715782798861382570559)
                      ·
                        rfl

theorem cell23_1115360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_1115360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115360 prefixEnd_1115360 := by exact prefixLift 1115360
  have htrace : WordTrace (prefixWord ++ tailWord_1115360) baseStart_1115360 baseEnd_1115360 := by
    simpa [prefixWord, tailWord_1115360, baseEnd_1115360] using wordTrace_append hprefix tailTrace_1115360
  have hstable : (prefixWord ++ tailWord_1115360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115360).length < 2 ^ (prefixWord ++ tailWord_1115360).sum := by decide
  have hdescent : baseEnd_1115360 < baseStart_1115360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115416 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1115416 : Nat := 118140960795 + 1115416 * 2 ^ 59
def prefixEnd_1115416 : Nat := 4983230072969 + 3 ^ 40 * 1115416 * 2
def baseEnd_1115416 : Nat := 572744537715513163470301

theorem tailTrace_1115416 : CollatzResearch.WordTrace tailWord_1115416 prefixEnd_1115416 572744537715513163470301 := by
  unfold tailWord_1115416
  simp only [CollatzResearch.WordTrace]
  refine ⟨20341281863522902365799051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27121709151363869821065401 20341281863522902365799051)
  ·
    refine ⟨30511922795284353548698577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20341281863522902365799051 30511922795284353548698577)
    ·
      refine ⟨22883942096463265161523933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30511922795284353548698577 22883942096463265161523933)
      ·
        refine ⟨8581478286173724435571475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22883942096463265161523933 8581478286173724435571475)
        ·
          refine ⟨12872217429260586653357213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8581478286173724435571475 12872217429260586653357213)
          ·
            refine ⟨4827081535972719995008955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12872217429260586653357213 4827081535972719995008955)
            ·
              refine ⟨7240622303959079992513433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4827081535972719995008955 7240622303959079992513433)
              ·
                refine ⟨5430466727969309994385075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7240622303959079992513433 5430466727969309994385075)
                ·
                  refine ⟨8145700091953964991577613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5430466727969309994385075 8145700091953964991577613)
                  ·
                    refine ⟨3054637534482736871841605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8145700091953964991577613 3054637534482736871841605)
                    ·
                      refine ⟨572744537715513163470301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3054637534482736871841605 572744537715513163470301)
                      ·
                        rfl

theorem cell23_1115416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1115416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115416 prefixEnd_1115416 := by exact prefixLift 1115416
  have htrace : WordTrace (prefixWord ++ tailWord_1115416) baseStart_1115416 baseEnd_1115416 := by
    simpa [prefixWord, tailWord_1115416, baseEnd_1115416] using wordTrace_append hprefix tailTrace_1115416
  have hstable : (prefixWord ++ tailWord_1115416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115416).length < 2 ^ (prefixWord ++ tailWord_1115416).sum := by decide
  have hdescent : baseEnd_1115416 < baseStart_1115416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115456 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 6]
def baseStart_1115456 : Nat := 118140960795 + 1115456 * 2 ^ 59
def prefixEnd_1115456 : Nat := 4983230072969 + 3 ^ 40 * 1115456 * 2
def baseEnd_1115456 : Nat := 63640564104632556330013

theorem tailTrace_1115456 : CollatzResearch.WordTrace tailWord_1115456 prefixEnd_1115456 63640564104632556330013 := by
  unfold tailWord_1115456
  simp only [CollatzResearch.WordTrace]
  refine ⟨20342011323450445781527111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27122681764600594375369481 20342011323450445781527111)
  ·
    refine ⟨30513016985175668672290667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20342011323450445781527111 30513016985175668672290667)
    ·
      refine ⟨45769525477763503008436001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30513016985175668672290667 45769525477763503008436001)
      ·
        refine ⟨34327144108322627256327001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45769525477763503008436001 34327144108322627256327001)
        ·
          refine ⟨25745358081241970442245251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34327144108322627256327001 25745358081241970442245251)
          ·
            refine ⟨38618037121862955663367877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25745358081241970442245251 38618037121862955663367877)
            ·
              refine ⟨7240881960349304186881477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38618037121862955663367877 7240881960349304186881477)
              ·
                refine ⟨1357665367565494535040277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7240881960349304186881477 1357665367565494535040277)
                ·
                  refine ⟨63640564104632556330013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1357665367565494535040277 63640564104632556330013)
                  ·
                    rfl

theorem cell23_1115456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 6].length) (baseStart_1115456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115456 prefixEnd_1115456 := by exact prefixLift 1115456
  have htrace : WordTrace (prefixWord ++ tailWord_1115456) baseStart_1115456 baseEnd_1115456 := by
    simpa [prefixWord, tailWord_1115456, baseEnd_1115456] using wordTrace_append hprefix tailTrace_1115456
  have hstable : (prefixWord ++ tailWord_1115456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115456).length < 2 ^ (prefixWord ++ tailWord_1115456).sum := by decide
  have hdescent : baseEnd_1115456 < baseStart_1115456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115516 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_1115516 : Nat := 118140960795 + 1115516 * 2 ^ 59
def prefixEnd_1115516 : Nat := 4983230072969 + 3 ^ 40 * 1115516 * 2
def baseEnd_1115516 : Nat := 190931961926987590739947

theorem tailTrace_1115516 : CollatzResearch.WordTrace tailWord_1115516 prefixEnd_1115516 190931961926987590739947 := by
  unfold tailWord_1115516
  simp only [CollatzResearch.WordTrace]
  refine ⟨20343105513341760905119201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27124140684455681206825601 20343105513341760905119201)
  ·
    refine ⟨15257329135006320678839401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20343105513341760905119201 15257329135006320678839401)
    ·
      refine ⟨11442996851254740509129551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15257329135006320678839401 11442996851254740509129551)
      ·
        refine ⟨17164495276882110763694327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11442996851254740509129551 17164495276882110763694327)
        ·
          refine ⟨25746742915323166145541491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17164495276882110763694327 25746742915323166145541491)
          ·
            refine ⟨38620114372984749218312237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25746742915323166145541491 38620114372984749218312237)
            ·
              refine ⟨14482542889869280956867089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38620114372984749218312237 14482542889869280956867089)
              ·
                refine ⟨10861907167401960717650317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14482542889869280956867089 10861907167401960717650317)
                ·
                  refine ⟨4073215187775735269118869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10861907167401960717650317 4073215187775735269118869)
                  ·
                    refine ⟨190931961926987590739947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4073215187775735269118869 190931961926987590739947)
                    ·
                      rfl

theorem cell23_1115516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_1115516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115516 prefixEnd_1115516 := by exact prefixLift 1115516
  have htrace : WordTrace (prefixWord ++ tailWord_1115516) baseStart_1115516 baseEnd_1115516 := by
    simpa [prefixWord, tailWord_1115516, baseEnd_1115516] using wordTrace_append hprefix tailTrace_1115516
  have hstable : (prefixWord ++ tailWord_1115516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115516).length < 2 ^ (prefixWord ++ tailWord_1115516).sum := by decide
  have hdescent : baseEnd_1115516 < baseStart_1115516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115517 : List Nat := [1, 4, 1, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_1115517 : Nat := 118140960795 + 1115517 * 2 ^ 59
def prefixEnd_1115517 : Nat := 4983230072969 + 3 ^ 40 * 1115517 * 2
def baseEnd_1115517 : Nat := 572796399261617268307337

theorem tailTrace_1115517 : CollatzResearch.WordTrace tailWord_1115517 prefixEnd_1115517 572796399261617268307337 := by
  unfold tailWord_1115517
  simp only [CollatzResearch.WordTrace]
  refine ⟨40686247499679898981024805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27124164999786599320683203 40686247499679898981024805)
  ·
    refine ⟨7628671406189981058942151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40686247499679898981024805 7628671406189981058942151)
    ·
      refine ⟨11443007109284971588413227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7628671406189981058942151 11443007109284971588413227)
      ·
        refine ⟨17164510663927457382619841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11443007109284971588413227 17164510663927457382619841)
        ·
          refine ⟨12873382997945593036964881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17164510663927457382619841 12873382997945593036964881)
          ·
            refine ⟨9655037248459194777723661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12873382997945593036964881 9655037248459194777723661)
            ·
              refine ⟨3620638968172198041646373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9655037248459194777723661 3620638968172198041646373)
              ·
                refine ⟨678869806532287132808695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3620638968172198041646373 678869806532287132808695)
                ·
                  refine ⟨1018304709798430699213043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678869806532287132808695 1018304709798430699213043)
                  ·
                    refine ⟨1527457064697646048819565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1018304709798430699213043 1527457064697646048819565)
                    ·
                      refine ⟨572796399261617268307337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1527457064697646048819565 572796399261617268307337)
                      ·
                        rfl

theorem cell23_1115517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_1115517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115517 prefixEnd_1115517 := by exact prefixLift 1115517
  have htrace : WordTrace (prefixWord ++ tailWord_1115517) baseStart_1115517 baseEnd_1115517 := by
    simpa [prefixWord, tailWord_1115517, baseEnd_1115517] using wordTrace_append hprefix tailTrace_1115517
  have hstable : (prefixWord ++ tailWord_1115517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115517).length < 2 ^ (prefixWord ++ tailWord_1115517).sum := by decide
  have hdescent : baseEnd_1115517 < baseStart_1115517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115523 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 4]
def baseStart_1115523 : Nat := 118140960795 + 1115523 * 2 ^ 59
def prefixEnd_1115523 : Nat := 4983230072969 + 3 ^ 40 * 1115523 * 2
def baseEnd_1115523 : Nat := 572799480145544244832309

theorem tailTrace_1115523 : CollatzResearch.WordTrace tailWord_1115523 prefixEnd_1115523 572799480145544244832309 := by
  unfold tailWord_1115523
  simp only [CollatzResearch.WordTrace]
  refine ⟨40686466337658162005743223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27124310891772108003828815 40686466337658162005743223)
  ·
    refine ⟨61029699506487243008614835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40686466337658162005743223 61029699506487243008614835)
    ·
      refine ⟨91544549259730864512922253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61029699506487243008614835 91544549259730864512922253)
      ·
        refine ⟨34329205972399074192345845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91544549259730864512922253 34329205972399074192345845)
        ·
          refine ⟨3218363059912413205532423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34329205972399074192345845 3218363059912413205532423)
          ·
            refine ⟨4827544589868619808298635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218363059912413205532423 4827544589868619808298635)
            ·
              refine ⟨7241316884802929712447953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4827544589868619808298635 7241316884802929712447953)
              ·
                refine ⟨5430987663602197284335965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7241316884802929712447953 5430987663602197284335965)
                ·
                  refine ⟨2036620373850823981625987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5430987663602197284335965 2036620373850823981625987)
                  ·
                    refine ⟨3054930560776235972438981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2036620373850823981625987 3054930560776235972438981)
                    ·
                      refine ⟨572799480145544244832309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3054930560776235972438981 572799480145544244832309)
                      ·
                        rfl

theorem cell23_1115523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_1115523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115523 prefixEnd_1115523 := by exact prefixLift 1115523
  have htrace : WordTrace (prefixWord ++ tailWord_1115523) baseStart_1115523 baseEnd_1115523 := by
    simpa [prefixWord, tailWord_1115523, baseEnd_1115523] using wordTrace_append hprefix tailTrace_1115523
  have hstable : (prefixWord ++ tailWord_1115523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115523).length < 2 ^ (prefixWord ++ tailWord_1115523).sum := by decide
  have hdescent : baseEnd_1115523 < baseStart_1115523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115540 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1115540 : Nat := 118140960795 + 1115540 * 2 ^ 59
def prefixEnd_1115540 : Nat := 4983230072969 + 3 ^ 40 * 1115540 * 2
def baseEnd_1115540 : Nat := 572808209316670678319731

theorem tailTrace_1115540 : CollatzResearch.WordTrace tailWord_1115540 prefixEnd_1115540 572808209316670678319731 := by
  unfold tailWord_1115540
  simp only [CollatzResearch.WordTrace]
  refine ⟨20343543189298286954556037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27124724252397715939408049 20343543189298286954556037)
  ·
    refine ⟨3814414347993428803979257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20343543189298286954556037 3814414347993428803979257)
    ·
      refine ⟨2860810760995071602984443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3814414347993428803979257 2860810760995071602984443)
      ·
        refine ⟨4291216141492607404476665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2860810760995071602984443 4291216141492607404476665)
        ·
          refine ⟨3218412106119455553357499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4291216141492607404476665 3218412106119455553357499)
          ·
            refine ⟨4827618159179183330036249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218412106119455553357499 4827618159179183330036249)
            ·
              refine ⟨3620713619384387497527187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4827618159179183330036249 3620713619384387497527187)
              ·
                refine ⟨5431070429076581246290781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3620713619384387497527187 5431070429076581246290781)
                ·
                  refine ⟨2036651410903717967359043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5431070429076581246290781 2036651410903717967359043)
                  ·
                    refine ⟨3054977116355576951038565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2036651410903717967359043 3054977116355576951038565)
                    ·
                      refine ⟨572808209316670678319731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3054977116355576951038565 572808209316670678319731)
                      ·
                        rfl

theorem cell23_1115540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1115540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115540 prefixEnd_1115540 := by exact prefixLift 1115540
  have htrace : WordTrace (prefixWord ++ tailWord_1115540) baseStart_1115540 baseEnd_1115540 := by
    simpa [prefixWord, tailWord_1115540, baseEnd_1115540] using wordTrace_append hprefix tailTrace_1115540
  have hstable : (prefixWord ++ tailWord_1115540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115540).length < 2 ^ (prefixWord ++ tailWord_1115540).sum := by decide
  have hdescent : baseEnd_1115540 < baseStart_1115540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115544 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1115544 : Nat := 118140960795 + 1115544 * 2 ^ 59
def prefixEnd_1115544 : Nat := 4983230072969 + 3 ^ 40 * 1115544 * 2
def baseEnd_1115544 : Nat := 572810263239288662669713

theorem tailTrace_1115544 : CollatzResearch.WordTrace tailWord_1115544 prefixEnd_1115544 572810263239288662669713 := by
  unfold tailWord_1115544
  simp only [CollatzResearch.WordTrace]
  refine ⟨20343616135291041296128843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27124821513721388394838457 20343616135291041296128843)
  ·
    refine ⟨30515424202936561944193265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20343616135291041296128843 30515424202936561944193265)
    ·
      refine ⟨22886568152202421458144949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30515424202936561944193265 22886568152202421458144949)
      ·
        refine ⟨2145615764268977011701089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22886568152202421458144949 2145615764268977011701089)
        ·
          refine ⟨1609211823201732758775817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2145615764268977011701089 1609211823201732758775817)
          ·
            refine ⟨1206908867401299569081863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1609211823201732758775817 1206908867401299569081863)
            ·
              refine ⟨1810363301101949353622795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206908867401299569081863 1810363301101949353622795)
              ·
                refine ⟨2715544951652924030434193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810363301101949353622795 2715544951652924030434193)
                ·
                  refine ⟨2036658713739693022825645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2715544951652924030434193 2036658713739693022825645)
                  ·
                    refine ⟨763747017652384883559617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036658713739693022825645 763747017652384883559617)
                    ·
                      refine ⟨572810263239288662669713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763747017652384883559617 572810263239288662669713)
                      ·
                        rfl

theorem cell23_1115544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1115544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115544 prefixEnd_1115544 := by exact prefixLift 1115544
  have htrace : WordTrace (prefixWord ++ tailWord_1115544) baseStart_1115544 baseEnd_1115544 := by
    simpa [prefixWord, tailWord_1115544, baseEnd_1115544] using wordTrace_append hprefix tailTrace_1115544
  have hstable : (prefixWord ++ tailWord_1115544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115544).length < 2 ^ (prefixWord ++ tailWord_1115544).sum := by decide
  have hdescent : baseEnd_1115544 < baseStart_1115544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115576 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 1, 9]
def baseStart_1115576 : Nat := 118140960795 + 1115576 * 2 ^ 59
def prefixEnd_1115576 : Nat := 4983230072969 + 3 ^ 40 * 1115576 * 2
def baseEnd_1115576 : Nat := 190942231540077512489855

theorem tailTrace_1115576 : CollatzResearch.WordTrace tailWord_1115576 prefixEnd_1115576 190942231540077512489855 := by
  unfold tailWord_1115576
  simp only [CollatzResearch.WordTrace]
  refine ⟨20344199703233076028711291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27125599604310768038281721 20344199703233076028711291)
  ·
    refine ⟨30516299554849614043066937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20344199703233076028711291 30516299554849614043066937)
    ·
      refine ⟨22887224666137210532300203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30516299554849614043066937 22887224666137210532300203)
      ·
        refine ⟨34330836999205815798450305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22887224666137210532300203 34330836999205815798450305)
        ·
          refine ⟨25748127749404361848837729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34330836999205815798450305 25748127749404361848837729)
          ·
            refine ⟨19311095812053271386628297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25748127749404361848837729 19311095812053271386628297)
            ·
              refine ⟨14483321859039953539971223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19311095812053271386628297 14483321859039953539971223)
              ·
                refine ⟨21724982788559930309956835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14483321859039953539971223 21724982788559930309956835)
                ·
                  refine ⟨32587474182839895464935253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21724982788559930309956835 32587474182839895464935253)
                  ·
                    refine ⟨190942231540077512489855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 32587474182839895464935253 190942231540077512489855)
                    ·
                      rfl

theorem cell23_1115576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_1115576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115576 prefixEnd_1115576 := by exact prefixLift 1115576
  have htrace : WordTrace (prefixWord ++ tailWord_1115576) baseStart_1115576 baseEnd_1115576 := by
    simpa [prefixWord, tailWord_1115576, baseEnd_1115576] using wordTrace_append hprefix tailTrace_1115576
  have hstable : (prefixWord ++ tailWord_1115576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115576).length < 2 ^ (prefixWord ++ tailWord_1115576).sum := by decide
  have hdescent : baseEnd_1115576 < baseStart_1115576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115617 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_1115617 : Nat := 118140960795 + 1115617 * 2 ^ 59
def prefixEnd_1115617 : Nat := 4983230072969 + 3 ^ 40 * 1115617 * 2
def baseEnd_1115617 : Nat := 572847747327066877056877

theorem tailTrace_1115617 : CollatzResearch.WordTrace tailWord_1115617 prefixEnd_1115617 572847747327066877056877 := by
  unfold tailWord_1115617
  simp only [CollatzResearch.WordTrace]
  refine ⟨40689894799317616059665105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27126596532878410706443403 40689894799317616059665105)
  ·
    refine ⟨30517421099488212044748829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40689894799317616059665105 30517421099488212044748829)
    ·
      refine ⟨11444032912308079516780811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30517421099488212044748829 11444032912308079516780811)
      ·
        refine ⟨17166049368462119275171217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11444032912308079516780811 17166049368462119275171217)
        ·
          refine ⟨12874537026346589456378413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17166049368462119275171217 12874537026346589456378413)
          ·
            refine ⟨4827951384879971046141905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12874537026346589456378413 4827951384879971046141905)
            ·
              refine ⟨3620963538659978284606429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4827951384879971046141905 3620963538659978284606429)
              ·
                refine ⟨1357861326997491856727411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3620963538659978284606429 1357861326997491856727411)
                ·
                  refine ⟨2036791990496237785091117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357861326997491856727411 2036791990496237785091117)
                  ·
                    refine ⟨763796996436089169409169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036791990496237785091117 763796996436089169409169)
                    ·
                      refine ⟨572847747327066877056877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763796996436089169409169 572847747327066877056877)
                      ·
                        rfl

theorem cell23_1115617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_1115617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115617 prefixEnd_1115617 := by exact prefixLift 1115617
  have htrace : WordTrace (prefixWord ++ tailWord_1115617) baseStart_1115617 baseEnd_1115617 := by
    simpa [prefixWord, tailWord_1115617, baseEnd_1115617] using wordTrace_append hprefix tailTrace_1115617
  have hstable : (prefixWord ++ tailWord_1115617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115617).length < 2 ^ (prefixWord ++ tailWord_1115617).sum := by decide
  have hdescent : baseEnd_1115617 < baseStart_1115617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115668 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1115668 : Nat := 118140960795 + 1115668 * 2 ^ 59
def prefixEnd_1115668 : Nat := 4983230072969 + 3 ^ 40 * 1115668 * 2
def baseEnd_1115668 : Nat := 572873934840446177519143

theorem tailTrace_1115668 : CollatzResearch.WordTrace tailWord_1115668 prefixEnd_1115668 572873934840446177519143 := by
  unfold tailWord_1115668
  simp only [CollatzResearch.WordTrace]
  refine ⟨20345877461066425884885829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27127836614755234513181105 20345877461066425884885829)
  ·
    refine ⟨3814852023949954853416093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20345877461066425884885829 3814852023949954853416093)
    ·
      refine ⟨1430569508981233070031035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3814852023949954853416093 1430569508981233070031035)
      ·
        refine ⟨2145854263471849605046553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430569508981233070031035 2145854263471849605046553)
        ·
          refine ⟨1609390697603887203784915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2145854263471849605046553 1609390697603887203784915)
          ·
            refine ⟨2414086046405830805677373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609390697603887203784915 2414086046405830805677373)
            ·
              refine ⟨905282267402186552129015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2414086046405830805677373 905282267402186552129015)
              ·
                refine ⟨1357923401103279828193523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905282267402186552129015 1357923401103279828193523)
                ·
                  refine ⟨2036885101654919742290285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357923401103279828193523 2036885101654919742290285)
                  ·
                    refine ⟨763831913120594903358857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036885101654919742290285 763831913120594903358857)
                    ·
                      refine ⟨572873934840446177519143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763831913120594903358857 572873934840446177519143)
                      ·
                        rfl

theorem cell23_1115668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1115668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115668 prefixEnd_1115668 := by exact prefixLift 1115668
  have htrace : WordTrace (prefixWord ++ tailWord_1115668) baseStart_1115668 baseEnd_1115668 := by
    simpa [prefixWord, tailWord_1115668, baseEnd_1115668] using wordTrace_append hprefix tailTrace_1115668
  have hstable : (prefixWord ++ tailWord_1115668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115668).length < 2 ^ (prefixWord ++ tailWord_1115668).sum := by decide
  have hdescent : baseEnd_1115668 < baseStart_1115668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115747 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 3, 4]
def baseStart_1115747 : Nat := 118140960795 + 1115747 * 2 ^ 59
def prefixEnd_1115747 : Nat := 4983230072969 + 3 ^ 40 * 1115747 * 2
def baseEnd_1115747 : Nat := 190971499937383789477093

theorem tailTrace_1115747 : CollatzResearch.WordTrace tailWord_1115747 prefixEnd_1115747 190971499937383789477093 := by
  unfold tailWord_1115747
  simp only [CollatzResearch.WordTrace]
  refine ⟨40694636288846648261897495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27129757525897765507931663 40694636288846648261897495)
  ·
    refine ⟨61041954433269972392846243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40694636288846648261897495 61041954433269972392846243)
    ·
      refine ⟨91562931649904958589269365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61041954433269972392846243 91562931649904958589269365)
      ·
        refine ⟨8584024842178589867744003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91562931649904958589269365 8584024842178589867744003)
        ·
          refine ⟨12876037263267884801616005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8584024842178589867744003 12876037263267884801616005)
          ·
            refine ⟨2414256986862728400303001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12876037263267884801616005 2414256986862728400303001)
            ·
              refine ⟨1810692740147046300227251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2414256986862728400303001 1810692740147046300227251)
              ·
                refine ⟨2716039110220569450340877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810692740147046300227251 2716039110220569450340877)
                ·
                  refine ⟨1018514666332713543877829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2716039110220569450340877 1018514666332713543877829)
                  ·
                    refine ⟨190971499937383789477093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1018514666332713543877829 190971499937383789477093)
                    ·
                      rfl

theorem cell23_1115747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 4].length) (baseStart_1115747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115747 prefixEnd_1115747 := by exact prefixLift 1115747
  have htrace : WordTrace (prefixWord ++ tailWord_1115747) baseStart_1115747 baseEnd_1115747 := by
    simpa [prefixWord, tailWord_1115747, baseEnd_1115747] using wordTrace_append hprefix tailTrace_1115747
  have hstable : (prefixWord ++ tailWord_1115747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115747).length < 2 ^ (prefixWord ++ tailWord_1115747).sum := by decide
  have hdescent : baseEnd_1115747 < baseStart_1115747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115850 : List Nat := [3, 1, 2, 1, 5, 11]
def baseStart_1115850 : Nat := 118140960795 + 1115850 * 2 ^ 59
def prefixEnd_1115850 : Nat := 4983230072969 + 3 ^ 40 * 1115850 * 2
def baseEnd_1115850 : Nat := 2357890486911787923635

theorem tailTrace_1115850 : CollatzResearch.WordTrace tailWord_1115850 prefixEnd_1115850 2357890486911787923635 := by
  unfold tailWord_1115850
  simp only [CollatzResearch.WordTrace]
  refine ⟨10174598251868374213224251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27132262004982331235264669 10174598251868374213224251)
  ·
    refine ⟨15261897377802561319836377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10174598251868374213224251 15261897377802561319836377)
    ·
      refine ⟨11446423033351920989877283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15261897377802561319836377 11446423033351920989877283)
      ·
        refine ⟨17169634550027881484815925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11446423033351920989877283 17169634550027881484815925)
        ·
          refine ⟨1609653239065113889201493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17169634550027881484815925 1609653239065113889201493)
          ·
            refine ⟨2357890486911787923635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1609653239065113889201493 2357890486911787923635)
            ·
              rfl

theorem cell23_1115850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 11].length) (baseStart_1115850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115850 prefixEnd_1115850 := by exact prefixLift 1115850
  have htrace : WordTrace (prefixWord ++ tailWord_1115850) baseStart_1115850 baseEnd_1115850 := by
    simpa [prefixWord, tailWord_1115850, baseEnd_1115850] using wordTrace_append hprefix tailTrace_1115850
  have hstable : (prefixWord ++ tailWord_1115850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115850).length < 2 ^ (prefixWord ++ tailWord_1115850).sum := by decide
  have hdescent : baseEnd_1115850 < baseStart_1115850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115854 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_1115854 : Nat := 118140960795 + 1115854 * 2 ^ 59
def prefixEnd_1115854 : Nat := 4983230072969 + 3 ^ 40 * 1115854 * 2
def baseEnd_1115854 : Nat := 190989814080727483264429

theorem tailTrace_1115854 : CollatzResearch.WordTrace tailWord_1115854 prefixEnd_1115854 190989814080727483264429 := by
  unfold tailWord_1115854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5087317362432375692005327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27132359266306003690695077 5087317362432375692005327)
  ·
    refine ⟨7630976043648563538007991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5087317362432375692005327 7630976043648563538007991)
    ·
      refine ⟨11446464065472845307011987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7630976043648563538007991 11446464065472845307011987)
      ·
        refine ⟨17169696098209267960517981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11446464065472845307011987 17169696098209267960517981)
        ·
          refine ⟨6438636036828475485194243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17169696098209267960517981 6438636036828475485194243)
          ·
            refine ⟨9657954055242713227791365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6438636036828475485194243 9657954055242713227791365)
            ·
              refine ⟨1810866385358008730210881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9657954055242713227791365 1810866385358008730210881)
              ·
                refine ⟨1358149789018506547658161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1810866385358008730210881 1358149789018506547658161)
                ·
                  refine ⟨1018612341763879910743621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1358149789018506547658161 1018612341763879910743621)
                  ·
                    refine ⟨190989814080727483264429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1018612341763879910743621 190989814080727483264429)
                    ·
                      rfl

theorem cell23_1115854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_1115854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115854 prefixEnd_1115854 := by exact prefixLift 1115854
  have htrace : WordTrace (prefixWord ++ tailWord_1115854) baseStart_1115854 baseEnd_1115854 := by
    simpa [prefixWord, tailWord_1115854, baseEnd_1115854] using wordTrace_append hprefix tailTrace_1115854
  have hstable : (prefixWord ++ tailWord_1115854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115854).length < 2 ^ (prefixWord ++ tailWord_1115854).sum := by decide
  have hdescent : baseEnd_1115854 < baseStart_1115854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115894 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1115894 : Nat := 118140960795 + 1115894 * 2 ^ 59
def prefixEnd_1115894 : Nat := 4983230072969 + 3 ^ 40 * 1115894 * 2
def baseEnd_1115894 : Nat := 572989981468362293293103

theorem tailTrace_1115894 : CollatzResearch.WordTrace tailWord_1115894 prefixEnd_1115894 572989981468362293293103 := by
  unfold tailWord_1115894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543749863707130772968671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27133331879542728244999157 2543749863707130772968671)
  ·
    refine ⟨3815624795560696159453007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2543749863707130772968671 3815624795560696159453007)
    ·
      refine ⟨5723437193341044239179511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3815624795560696159453007 5723437193341044239179511)
      ·
        refine ⟨8585155790011566358769267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5723437193341044239179511 8585155790011566358769267)
        ·
          refine ⟨12877733685017349538153901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8585155790011566358769267 12877733685017349538153901)
          ·
            refine ⟨4829150131881506076807713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12877733685017349538153901 4829150131881506076807713)
            ·
              refine ⟨3621862598911129557605785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4829150131881506076807713 3621862598911129557605785)
              ·
                refine ⟨2716396949183347168204339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3621862598911129557605785 2716396949183347168204339)
                ·
                  refine ⟨4074595423775020752306509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716396949183347168204339 4074595423775020752306509)
                  ·
                    refine ⟨1527973283915632782114941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4074595423775020752306509 1527973283915632782114941)
                    ·
                      refine ⟨572989981468362293293103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1527973283915632782114941 572989981468362293293103)
                      ·
                        rfl

theorem cell23_1115894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1115894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115894 prefixEnd_1115894 := by exact prefixLift 1115894
  have htrace : WordTrace (prefixWord ++ tailWord_1115894) baseStart_1115894 baseEnd_1115894 := by
    simpa [prefixWord, tailWord_1115894, baseEnd_1115894] using wordTrace_append hprefix tailTrace_1115894
  have hstable : (prefixWord ++ tailWord_1115894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115894).length < 2 ^ (prefixWord ++ tailWord_1115894).sum := by decide
  have hdescent : baseEnd_1115894 < baseStart_1115894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115904 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 1, 3, 2]
def baseStart_1115904 : Nat := 118140960795 + 1115904 * 2 ^ 59
def prefixEnd_1115904 : Nat := 4983230072969 + 3 ^ 40 * 1115904 * 2
def baseEnd_1115904 : Nat := 572995116274907254168057

theorem tailTrace_1115904 : CollatzResearch.WordTrace tailWord_1115904 prefixEnd_1115904 572995116274907254168057 := by
  unfold tailWord_1115904
  simp only [CollatzResearch.WordTrace]
  refine ⟨20350181274638932037681383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27133575032851909383575177 20350181274638932037681383)
  ·
    refine ⟨30525271911958398056522075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20350181274638932037681383 30525271911958398056522075)
    ·
      refine ⟨45787907867937597084783113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30525271911958398056522075 45787907867937597084783113)
      ·
        refine ⟨34340930900953197813587335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45787907867937597084783113 34340930900953197813587335)
        ·
          refine ⟨51511396351429796720381003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34340930900953197813587335 51511396351429796720381003)
          ·
            refine ⟨77267094527144695080571505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51511396351429796720381003 77267094527144695080571505)
            ·
              refine ⟨57950320895358521310428629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77267094527144695080571505 57950320895358521310428629)
              ·
                refine ⟨1358210645984965343213171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57950320895358521310428629 1358210645984965343213171)
                ·
                  refine ⟨2037315968977448014819757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358210645984965343213171 2037315968977448014819757)
                  ·
                    refine ⟨763993488366543005557409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037315968977448014819757 763993488366543005557409)
                    ·
                      refine ⟨572995116274907254168057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 763993488366543005557409 572995116274907254168057)
                      ·
                        rfl

theorem cell23_1115904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_1115904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115904 prefixEnd_1115904 := by exact prefixLift 1115904
  have htrace : WordTrace (prefixWord ++ tailWord_1115904) baseStart_1115904 baseEnd_1115904 := by
    simpa [prefixWord, tailWord_1115904, baseEnd_1115904] using wordTrace_append hprefix tailTrace_1115904
  have hstable : (prefixWord ++ tailWord_1115904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115904).length < 2 ^ (prefixWord ++ tailWord_1115904).sum := by decide
  have hdescent : baseEnd_1115904 < baseStart_1115904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115911 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1115911 : Nat := 118140960795 + 1115911 * 2 ^ 59
def prefixEnd_1115911 : Nat := 4983230072969 + 3 ^ 40 * 1115911 * 2
def baseEnd_1115911 : Nat := 572998710639488726780525

theorem tailTrace_1115911 : CollatzResearch.WordTrace tailWord_1115911 prefixEnd_1115911 572998710639488726780525 := by
  unfold tailWord_1115911
  simp only [CollatzResearch.WordTrace]
  refine ⟨40700617860252504270867587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27133745240168336180578391 40700617860252504270867587)
  ·
    refine ⟨61050926790378756406301381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40700617860252504270867587 61050926790378756406301381)
    ·
      refine ⟨11447048773196016826181509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61050926790378756406301381 11447048773196016826181509)
      ·
        refine ⟨2146321644974253154909033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11447048773196016826181509 2146321644974253154909033)
        ·
          refine ⟨1609741233730689866181775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2146321644974253154909033 1609741233730689866181775)
          ·
            refine ⟨2414611850596034799272663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609741233730689866181775 2414611850596034799272663)
            ·
              refine ⟨3621917775894052198908995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414611850596034799272663 3621917775894052198908995)
              ·
                refine ⟨5432876663841078298363493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621917775894052198908995 5432876663841078298363493)
                ·
                  refine ⟨1018664374470202180943155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5432876663841078298363493 1018664374470202180943155)
                  ·
                    refine ⟨1527996561705303271414733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1018664374470202180943155 1527996561705303271414733)
                    ·
                      refine ⟨572998710639488726780525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1527996561705303271414733 572998710639488726780525)
                      ·
                        rfl

theorem cell23_1115911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1115911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115911 prefixEnd_1115911 := by exact prefixLift 1115911
  have htrace : WordTrace (prefixWord ++ tailWord_1115911) baseStart_1115911 baseEnd_1115911 := by
    simpa [prefixWord, tailWord_1115911, baseEnd_1115911] using wordTrace_append hprefix tailTrace_1115911
  have hstable : (prefixWord ++ tailWord_1115911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115911).length < 2 ^ (prefixWord ++ tailWord_1115911).sum := by decide
  have hdescent : baseEnd_1115911 < baseStart_1115911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115927 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 2, 6]
def baseStart_1115927 : Nat := 118140960795 + 1115927 * 2 ^ 59
def prefixEnd_1115927 : Nat := 4983230072969 + 3 ^ 40 * 1115927 * 2
def baseEnd_1115927 : Nat := 191002308776653554726817

theorem tailTrace_1115927 : CollatzResearch.WordTrace tailWord_1115927 prefixEnd_1115927 191002308776653554726817 := by
  unfold tailWord_1115927
  simp only [CollatzResearch.WordTrace]
  refine ⟨40701201428194539003450035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27134134285463026002300023 40701201428194539003450035)
  ·
    refine ⟨61051802142291808505175053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40701201428194539003450035 61051802142291808505175053)
    ·
      refine ⟨22894425803359428189440645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61051802142291808505175053 22894425803359428189440645)
      ·
        refine ⟨4292704838129892785520121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22894425803359428189440645 4292704838129892785520121)
        ·
          refine ⟨3219528628597419589140091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4292704838129892785520121 3219528628597419589140091)
          ·
            refine ⟨4829292942896129383710137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219528628597419589140091 4829292942896129383710137)
            ·
              refine ⟨3621969707172097037782603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4829292942896129383710137 3621969707172097037782603)
              ·
                refine ⟨5432954560758145556673905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621969707172097037782603 5432954560758145556673905)
                ·
                  refine ⟨4074715920568609167505429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432954560758145556673905 4074715920568609167505429)
                  ·
                    refine ⟨191002308776653554726817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4074715920568609167505429 191002308776653554726817)
                    ·
                      rfl

theorem cell23_1115927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_1115927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115927 prefixEnd_1115927 := by exact prefixLift 1115927
  have htrace : WordTrace (prefixWord ++ tailWord_1115927) baseStart_1115927 baseEnd_1115927 := by
    simpa [prefixWord, tailWord_1115927, baseEnd_1115927] using wordTrace_append hprefix tailTrace_1115927
  have hstable : (prefixWord ++ tailWord_1115927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115927).length < 2 ^ (prefixWord ++ tailWord_1115927).sum := by decide
  have hdescent : baseEnd_1115927 < baseStart_1115927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115985 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 2, 2, 2]
def baseStart_1115985 : Nat := 118140960795 + 1115985 * 2 ^ 59
def prefixEnd_1115985 : Nat := 4983230072969 + 3 ^ 40 * 1115985 * 2
def baseEnd_1115985 : Nat := 573036708207921437255185

theorem tailTrace_1115985 : CollatzResearch.WordTrace tailWord_1115985 prefixEnd_1115985 573036708207921437255185 := by
  unfold tailWord_1115985
  simp only [CollatzResearch.WordTrace]
  refine ⟨40703316861984414909061409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27135544574656276606040939 40703316861984414909061409)
  ·
    refine ⟨30527487646488311181796057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40703316861984414909061409 30527487646488311181796057)
    ·
      refine ⟨22895615734866233386347043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30527487646488311181796057 22895615734866233386347043)
      ·
        refine ⟨34343423602299350079520565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22895615734866233386347043 34343423602299350079520565)
        ·
          refine ⟨3219695962715564069955053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34343423602299350079520565 3219695962715564069955053)
          ·
            refine ⟨1207385986018336526233145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3219695962715564069955053 1207385986018336526233145)
            ·
              refine ⟨905539489513752394674859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207385986018336526233145 905539489513752394674859)
              ·
                refine ⟨1358309234270628592012289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905539489513752394674859 1358309234270628592012289)
                ·
                  refine ⟨1018731925702971444009217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1358309234270628592012289 1018731925702971444009217)
                  ·
                    refine ⟨764048944277228583006913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1018731925702971444009217 764048944277228583006913)
                    ·
                      refine ⟨573036708207921437255185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764048944277228583006913 573036708207921437255185)
                      ·
                        rfl

theorem cell23_1115985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_1115985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1115985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1115985 prefixEnd_1115985 := by exact prefixLift 1115985
  have htrace : WordTrace (prefixWord ++ tailWord_1115985) baseStart_1115985 baseEnd_1115985 := by
    simpa [prefixWord, tailWord_1115985, baseEnd_1115985] using wordTrace_append hprefix tailTrace_1115985
  have hstable : (prefixWord ++ tailWord_1115985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115985).length < 2 ^ (prefixWord ++ tailWord_1115985).sum := by decide
  have hdescent : baseEnd_1115985 < baseStart_1115985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116014 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1116014 : Nat := 118140960795 + 1116014 * 2 ^ 59
def prefixEnd_1116014 : Nat := 4983230072969 + 3 ^ 40 * 1116014 * 2
def baseEnd_1116014 : Nat := 573051599146901823792551

theorem tailTrace_1116014 : CollatzResearch.WordTrace tailWord_1116014 prefixEnd_1116014 573051599146901823792551 := by
  unfold tailWord_1116014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088046822359919107733387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27136249719252901907911397 5088046822359919107733387)
  ·
    refine ⟨7632070233539878661600081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5088046822359919107733387 7632070233539878661600081)
    ·
      refine ⟨5724052675154908996200061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7632070233539878661600081 5724052675154908996200061)
      ·
        refine ⟨2146519753183090873575023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5724052675154908996200061 2146519753183090873575023)
        ·
          refine ⟨3219779629774636310362535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2146519753183090873575023 3219779629774636310362535)
          ·
            refine ⟨4829669444661954465543803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219779629774636310362535 4829669444661954465543803)
            ·
              refine ⟨7244504166992931698315705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4829669444661954465543803 7244504166992931698315705)
              ·
                refine ⟨5433378125244698773736779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7244504166992931698315705 5433378125244698773736779)
                ·
                  refine ⟨8150067187867048160605169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5433378125244698773736779 8150067187867048160605169)
                  ·
                    refine ⟨6112550390900286120453877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8150067187867048160605169 6112550390900286120453877)
                    ·
                      refine ⟨573051599146901823792551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6112550390900286120453877 573051599146901823792551)
                      ·
                        rfl

theorem cell23_1116014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1116014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116014 prefixEnd_1116014 := by exact prefixLift 1116014
  have htrace : WordTrace (prefixWord ++ tailWord_1116014) baseStart_1116014 baseEnd_1116014 := by
    simpa [prefixWord, tailWord_1116014, baseEnd_1116014] using wordTrace_append hprefix tailTrace_1116014
  have hstable : (prefixWord ++ tailWord_1116014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116014).length < 2 ^ (prefixWord ++ tailWord_1116014).sum := by decide
  have hdescent : baseEnd_1116014 < baseStart_1116014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116027 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 3]
def baseStart_1116027 : Nat := 118140960795 + 1116027 * 2 ^ 59
def prefixEnd_1116027 : Nat := 4983230072969 + 3 ^ 40 * 1116027 * 2
def baseEnd_1116027 : Nat := 573058274395410272929991

theorem tailTrace_1116027 : CollatzResearch.WordTrace tailWord_1116027 prefixEnd_1116027 573058274395410272929991 := by
  unfold tailWord_1116027
  simp only [CollatzResearch.WordTrace]
  refine ⟨40704848727832256082090335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27136565818554837388060223 40704848727832256082090335)
  ·
    refine ⟨61057273091748384123135503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40704848727832256082090335 61057273091748384123135503)
    ·
      refine ⟨91585909637622576184703255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61057273091748384123135503 91585909637622576184703255)
      ·
        refine ⟨137378864456433864277054883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91585909637622576184703255 137378864456433864277054883)
        ·
          refine ⟨206068296684650796415582325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137378864456433864277054883 206068296684650796415582325)
          ·
            refine ⟨19318902814186012163960843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206068296684650796415582325 19318902814186012163960843)
            ·
              refine ⟨28978354221279018245941265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19318902814186012163960843 28978354221279018245941265)
              ·
                refine ⟨21733765665959263684455949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28978354221279018245941265 21733765665959263684455949)
                ·
                  refine ⟨8150162124734723881670981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21733765665959263684455949 8150162124734723881670981)
                  ·
                    refine ⟨1528155398387760727813309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8150162124734723881670981 1528155398387760727813309)
                    ·
                      refine ⟨573058274395410272929991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1528155398387760727813309 573058274395410272929991)
                      ·
                        rfl

theorem cell23_1116027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 3].length) (baseStart_1116027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116027 prefixEnd_1116027 := by exact prefixLift 1116027
  have htrace : WordTrace (prefixWord ++ tailWord_1116027) baseStart_1116027 baseEnd_1116027 := by
    simpa [prefixWord, tailWord_1116027, baseEnd_1116027] using wordTrace_append hprefix tailTrace_1116027
  have hstable : (prefixWord ++ tailWord_1116027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116027).length < 2 ^ (prefixWord ++ tailWord_1116027).sum := by decide
  have hdescent : baseEnd_1116027 < baseStart_1116027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116061 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1116061 : Nat := 118140960795 + 1116061 * 2 ^ 59
def prefixEnd_1116061 : Nat := 4983230072969 + 3 ^ 40 * 1116061 * 2
def baseEnd_1116061 : Nat := 573075732737663139904835

theorem tailTrace_1116061 : CollatzResearch.WordTrace tailWord_1116061 prefixEnd_1116061 573075732737663139904835 := by
  unfold tailWord_1116061
  simp only [CollatzResearch.WordTrace]
  refine ⟨40706088809709079888828037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27137392539806053259218691 40706088809709079888828037)
  ·
    refine ⟨7632391651820452479155257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40706088809709079888828037 7632391651820452479155257)
    ·
      refine ⟨5724293738865339359366443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7632391651820452479155257 5724293738865339359366443)
      ·
        refine ⟨8586440608298009039049665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5724293738865339359366443 8586440608298009039049665)
        ·
          refine ⟨6439830456223506779287249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8586440608298009039049665 6439830456223506779287249)
          ·
            refine ⟨4829872842167630084465437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6439830456223506779287249 4829872842167630084465437)
            ·
              refine ⟨1811202315812861281674539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4829872842167630084465437 1811202315812861281674539)
              ·
                refine ⟨2716803473719291922511809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811202315812861281674539 2716803473719291922511809)
                ·
                  refine ⟨2037602605289468941883857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2716803473719291922511809 2037602605289468941883857)
                  ·
                    refine ⟨1528201953967101706412893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2037602605289468941883857 1528201953967101706412893)
                    ·
                      refine ⟨573075732737663139904835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1528201953967101706412893 573075732737663139904835)
                      ·
                        rfl

theorem cell23_1116061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1116061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116061 prefixEnd_1116061 := by exact prefixLift 1116061
  have htrace : WordTrace (prefixWord ++ tailWord_1116061) baseStart_1116061 baseEnd_1116061 := by
    simpa [prefixWord, tailWord_1116061, baseEnd_1116061] using wordTrace_append hprefix tailTrace_1116061
  have hstable : (prefixWord ++ tailWord_1116061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116061).length < 2 ^ (prefixWord ++ tailWord_1116061).sum := by decide
  have hdescent : baseEnd_1116061 < baseStart_1116061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116068 : List Nat := [2, 3, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_1116068 : Nat := 118140960795 + 1116068 * 2 ^ 59
def prefixEnd_1116068 : Nat := 4983230072969 + 3 ^ 40 * 1116068 * 2
def baseEnd_1116068 : Nat := 191026442367414870839101

theorem tailTrace_1116068 : CollatzResearch.WordTrace tailWord_1116068 prefixEnd_1116068 191026442367414870839101 := by
  unfold tailWord_1116068
  simp only [CollatzResearch.WordTrace]
  refine ⟨20353172060341860042166429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27137562747122480056221905 20353172060341860042166429)
  ·
    refine ⟨7632439522628197515812411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20353172060341860042166429 7632439522628197515812411)
    ·
      refine ⟨11448659283942296273718617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7632439522628197515812411 11448659283942296273718617)
      ·
        refine ⟨8586494462956722205288963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11448659283942296273718617 8586494462956722205288963)
        ·
          refine ⟨12879741694435083307933445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8586494462956722205288963 12879741694435083307933445)
          ·
            refine ⟨2414951567706578120237521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12879741694435083307933445 2414951567706578120237521)
            ·
              refine ⟨1811213675779933590178141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2414951567706578120237521 1811213675779933590178141)
              ·
                refine ⟨679205128417475096316803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1811213675779933590178141 679205128417475096316803)
                ·
                  refine ⟨1018807692626212644475205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679205128417475096316803 1018807692626212644475205)
                  ·
                    refine ⟨191026442367414870839101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1018807692626212644475205 191026442367414870839101)
                    ·
                      rfl

theorem cell23_1116068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_1116068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116068 prefixEnd_1116068 := by exact prefixLift 1116068
  have htrace : WordTrace (prefixWord ++ tailWord_1116068) baseStart_1116068 baseEnd_1116068 := by
    simpa [prefixWord, tailWord_1116068, baseEnd_1116068] using wordTrace_append hprefix tailTrace_1116068
  have hstable : (prefixWord ++ tailWord_1116068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116068).length < 2 ^ (prefixWord ++ tailWord_1116068).sum := by decide
  have hdescent : baseEnd_1116068 < baseStart_1116068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116081 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 6]
def baseStart_1116081 : Nat := 118140960795 + 1116081 * 2 ^ 59
def prefixEnd_1116081 : Nat := 4983230072969 + 3 ^ 40 * 1116081 * 2
def baseEnd_1116081 : Nat := 63676222483417006850527

theorem tailTrace_1116081 : CollatzResearch.WordTrace tailWord_1116081 prefixEnd_1116081 63676222483417006850527 := by
  unfold tailWord_1116081
  simp only [CollatzResearch.WordTrace]
  refine ⟨40706818269636623304556097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27137878846424415536370731 40706818269636623304556097)
  ·
    refine ⟨30530113702227467478417073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40706818269636623304556097 30530113702227467478417073)
    ·
      refine ⟨22897585276670600608812805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30530113702227467478417073 22897585276670600608812805)
      ·
        refine ⟨4293297239375737614152401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22897585276670600608812805 4293297239375737614152401)
        ·
          refine ⟨3219972929531803210614301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4293297239375737614152401 3219972929531803210614301)
          ·
            refine ⟨1207489848574426203980363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3219972929531803210614301 1207489848574426203980363)
            ·
              refine ⟨1811234772861639305970545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207489848574426203980363 1811234772861639305970545)
              ·
                refine ⟨1358426079646229479477909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1811234772861639305970545 1358426079646229479477909)
                ·
                  refine ⟨63676222483417006850527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1358426079646229479477909 63676222483417006850527)
                  ·
                    rfl

theorem cell23_1116081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 6].length) (baseStart_1116081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116081 prefixEnd_1116081 := by exact prefixLift 1116081
  have htrace : WordTrace (prefixWord ++ tailWord_1116081) baseStart_1116081 baseEnd_1116081 := by
    simpa [prefixWord, tailWord_1116081, baseEnd_1116081] using wordTrace_append hprefix tailTrace_1116081
  have hstable : (prefixWord ++ tailWord_1116081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116081).length < 2 ^ (prefixWord ++ tailWord_1116081).sum := by decide
  have hdescent : baseEnd_1116081 < baseStart_1116081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116131 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1116131 : Nat := 118140960795 + 1116131 * 2 ^ 59
def prefixEnd_1116131 : Nat := 4983230072969 + 3 ^ 40 * 1116131 * 2
def baseEnd_1116131 : Nat := 573111676383477866029513

theorem tailTrace_1116131 : CollatzResearch.WordTrace tailWord_1116131 prefixEnd_1116131 573111676383477866029513 := by
  unfold tailWord_1116131
  simp only [CollatzResearch.WordTrace]
  refine ⟨40708641919455481843876247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27139094612970321229250831 40708641919455481843876247)
  ·
    refine ⟨61062962879183222765814371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40708641919455481843876247 61062962879183222765814371)
    ·
      refine ⟨91594444318774834148721557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61062962879183222765814371 91594444318774834148721557)
      ·
        refine ⟨4293489577442570350721323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91594444318774834148721557 4293489577442570350721323)
        ·
          refine ⟨6440234366163855526081985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293489577442570350721323 6440234366163855526081985)
          ·
            refine ⟨4830175774622891644561489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6440234366163855526081985 4830175774622891644561489)
            ·
              refine ⟨3622631830967168733421117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4830175774622891644561489 3622631830967168733421117)
              ·
                refine ⟨1358486936612688275032919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3622631830967168733421117 1358486936612688275032919)
                ·
                  refine ⟨2037730404919032412549379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358486936612688275032919 2037730404919032412549379)
                  ·
                    refine ⟨3056595607378548618824069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2037730404919032412549379 3056595607378548618824069)
                    ·
                      refine ⟨573111676383477866029513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3056595607378548618824069 573111676383477866029513)
                      ·
                        rfl

theorem cell23_1116131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1116131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116131 prefixEnd_1116131 := by exact prefixLift 1116131
  have htrace : WordTrace (prefixWord ++ tailWord_1116131) baseStart_1116131 baseEnd_1116131 := by
    simpa [prefixWord, tailWord_1116131, baseEnd_1116131] using wordTrace_append hprefix tailTrace_1116131
  have hstable : (prefixWord ++ tailWord_1116131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116131).length < 2 ^ (prefixWord ++ tailWord_1116131).sum := by decide
  have hdescent : baseEnd_1116131 < baseStart_1116131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116142 : List Nat := [4, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_1116142 : Nat := 118140960795 + 1116142 * 2 ^ 59
def prefixEnd_1116142 : Nat := 4983230072969 + 3 ^ 40 * 1116142 * 2
def baseEnd_1116142 : Nat := 573117324670677322991963

theorem tailTrace_1116142 : CollatzResearch.WordTrace tailWord_1116142 prefixEnd_1116142 573117324670677322991963 := by
  unfold tailWord_1116142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088630390301953840315835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27139362081610420481684453 5088630390301953840315835)
  ·
    refine ⟨7632945585452930760473753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5088630390301953840315835 7632945585452930760473753)
    ·
      refine ⟨5724709189089698070355315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7632945585452930760473753 5724709189089698070355315)
      ·
        refine ⟨8587063783634547105532973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5724709189089698070355315 8587063783634547105532973)
        ·
          refine ⟨3220148918862955164574865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8587063783634547105532973 3220148918862955164574865)
          ·
            refine ⟨2415111689147216373431149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3220148918862955164574865 2415111689147216373431149)
            ·
              refine ⟨905666883430206140036681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2415111689147216373431149 905666883430206140036681)
              ·
                refine ⟨679250162572654605027511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905666883430206140036681 679250162572654605027511)
                ·
                  refine ⟨1018875243858981907541267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679250162572654605027511 1018875243858981907541267)
                  ·
                    refine ⟨1528312865788472861311901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1018875243858981907541267 1528312865788472861311901)
                    ·
                      refine ⟨573117324670677322991963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1528312865788472861311901 573117324670677322991963)
                      ·
                        rfl

theorem cell23_1116142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_1116142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116142 prefixEnd_1116142 := by exact prefixLift 1116142
  have htrace : WordTrace (prefixWord ++ tailWord_1116142) baseStart_1116142 baseEnd_1116142 := by
    simpa [prefixWord, tailWord_1116142, baseEnd_1116142] using wordTrace_append hprefix tailTrace_1116142
  have hstable : (prefixWord ++ tailWord_1116142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116142).length < 2 ^ (prefixWord ++ tailWord_1116142).sum := by decide
  have hdescent : baseEnd_1116142 < baseStart_1116142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116199 : List Nat := [1, 1, 7, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_1116199 : Nat := 118140960795 + 1116199 * 2 ^ 59
def prefixEnd_1116199 : Nat := 4983230072969 + 3 ^ 40 * 1116199 * 2
def baseEnd_1116199 : Nat := 573146593067983599979201

theorem tailTrace_1116199 : CollatzResearch.WordTrace tailWord_1116199 prefixEnd_1116199 573146593067983599979201 := by
  unfold tailWord_1116199
  simp only [CollatzResearch.WordTrace]
  refine ⟨40711122083209129457351651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27140748055472752971567767 40711122083209129457351651)
  ·
    refine ⟨61066683124813694186027477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40711122083209129457351651 61066683124813694186027477)
    ·
      refine ⟨1431250385737820957485019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 61066683124813694186027477 1431250385737820957485019)
      ·
        refine ⟨2146875578606731436227529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1431250385737820957485019 2146875578606731436227529)
        ·
          refine ⟨1610156683955048577170647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2146875578606731436227529 1610156683955048577170647)
          ·
            refine ⟨2415235025932572865755971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610156683955048577170647 2415235025932572865755971)
            ·
              refine ⟨3622852538898859298633957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415235025932572865755971 3622852538898859298633957)
              ·
                refine ⟨679284851043536118493867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3622852538898859298633957 679284851043536118493867)
                ·
                  refine ⟨1018927276565304177740801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679284851043536118493867 1018927276565304177740801)
                  ·
                    refine ⟨764195457423978133305601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1018927276565304177740801 764195457423978133305601)
                    ·
                      refine ⟨573146593067983599979201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764195457423978133305601 573146593067983599979201)
                      ·
                        rfl

theorem cell23_1116199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_1116199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116199 prefixEnd_1116199 := by exact prefixLift 1116199
  have htrace : WordTrace (prefixWord ++ tailWord_1116199) baseStart_1116199 baseEnd_1116199 := by
    simpa [prefixWord, tailWord_1116199, baseEnd_1116199] using wordTrace_append hprefix tailTrace_1116199
  have hstable : (prefixWord ++ tailWord_1116199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116199).length < 2 ^ (prefixWord ++ tailWord_1116199).sum := by decide
  have hdescent : baseEnd_1116199 < baseStart_1116199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116234 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1116234 : Nat := 118140960795 + 1116234 * 2 ^ 59
def prefixEnd_1116234 : Nat := 4983230072969 + 3 ^ 40 * 1116234 * 2
def baseEnd_1116234 : Nat := 573164564890890963041539

theorem tailTrace_1116234 : CollatzResearch.WordTrace tailWord_1116234 prefixEnd_1116234 573164564890890963041539 := by
  unfold tailWord_1116234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178099659520582608718939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27141599092054886956583837 10178099659520582608718939)
  ·
    refine ⟨15267149489280873913078409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10178099659520582608718939 15267149489280873913078409)
    ·
      refine ⟨11450362116960655434808807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15267149489280873913078409 11450362116960655434808807)
      ·
        refine ⟨17175543175440983152213211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450362116960655434808807 17175543175440983152213211)
        ·
          refine ⟨25763314763161474728319817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17175543175440983152213211 25763314763161474728319817)
          ·
            refine ⟨19322486072371106046239863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25763314763161474728319817 19322486072371106046239863)
            ·
              refine ⟨28983729108556659069359795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19322486072371106046239863 28983729108556659069359795)
              ·
                refine ⟨43475593662834988604039693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28983729108556659069359795 43475593662834988604039693)
                ·
                  refine ⟨16303347623563120726514885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43475593662834988604039693 16303347623563120726514885)
                  ·
                    refine ⟨3056877679418085136221541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16303347623563120726514885 3056877679418085136221541)
                    ·
                      refine ⟨573164564890890963041539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3056877679418085136221541 573164564890890963041539)
                      ·
                        rfl

theorem cell23_1116234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1116234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116234 prefixEnd_1116234 := by exact prefixLift 1116234
  have htrace : WordTrace (prefixWord ++ tailWord_1116234) baseStart_1116234 baseEnd_1116234 := by
    simpa [prefixWord, tailWord_1116234, baseEnd_1116234] using wordTrace_append hprefix tailTrace_1116234
  have hstable : (prefixWord ++ tailWord_1116234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116234).length < 2 ^ (prefixWord ++ tailWord_1116234).sum := by decide
  have hdescent : baseEnd_1116234 < baseStart_1116234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116238 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_1116238 : Nat := 118140960795 + 1116238 * 2 ^ 59
def prefixEnd_1116238 : Nat := 4983230072969 + 3 ^ 40 * 1116238 * 2
def baseEnd_1116238 : Nat := 573166618813508947391521

theorem tailTrace_1116238 : CollatzResearch.WordTrace tailWord_1116238 prefixEnd_1116238 573166618813508947391521 := by
  unfold tailWord_1116238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089068066258479889752671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27141696353378559412014245 5089068066258479889752671)
  ·
    refine ⟨7633602099387719834629007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5089068066258479889752671 7633602099387719834629007)
    ·
      refine ⟨11450403149081579751943511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7633602099387719834629007 11450403149081579751943511)
      ·
        refine ⟨17175604723622369627915267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450403149081579751943511 17175604723622369627915267)
        ·
          refine ⟨25763407085433554441872901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17175604723622369627915267 25763407085433554441872901)
          ·
            refine ⟨4830638828518791457851169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25763407085433554441872901 4830638828518791457851169)
            ·
              refine ⟨3622979121389093593388377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4830638828518791457851169 3622979121389093593388377)
              ·
                refine ⟨2717234341041820195041283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3622979121389093593388377 2717234341041820195041283)
                ·
                  refine ⟨4075851511562730292561925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717234341041820195041283 4075851511562730292561925)
                  ·
                    refine ⟨764222158418011929855361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075851511562730292561925 764222158418011929855361)
                    ·
                      refine ⟨573166618813508947391521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764222158418011929855361 573166618813508947391521)
                      ·
                        rfl

theorem cell23_1116238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_1116238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116238 prefixEnd_1116238 := by exact prefixLift 1116238
  have htrace : WordTrace (prefixWord ++ tailWord_1116238) baseStart_1116238 baseEnd_1116238 := by
    simpa [prefixWord, tailWord_1116238, baseEnd_1116238] using wordTrace_append hprefix tailTrace_1116238
  have hstable : (prefixWord ++ tailWord_1116238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116238).length < 2 ^ (prefixWord ++ tailWord_1116238).sum := by decide
  have hdescent : baseEnd_1116238 < baseStart_1116238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116244 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 11]
def baseStart_1116244 : Nat := 118140960795 + 1116244 * 2 ^ 59
def prefixEnd_1116244 : Nat := 4983230072969 + 3 ^ 40 * 1116244 * 2
def baseEnd_1116244 : Nat := 63685522188603991546277

theorem tailTrace_1116244 : CollatzResearch.WordTrace tailWord_1116244 prefixEnd_1116244 63685522188603991546277 := by
  unfold tailWord_1116244
  simp only [CollatzResearch.WordTrace]
  refine ⟨20356381684023051071369893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27141842245364068095159857 20356381684023051071369893)
  ·
    refine ⟨3816821565754322075881855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20356381684023051071369893 3816821565754322075881855)
    ·
      refine ⟨5725232348631483113822783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3816821565754322075881855 5725232348631483113822783)
      ·
        refine ⟨8587848522947224670734175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5725232348631483113822783 8587848522947224670734175)
        ·
          refine ⟨12881772784420837006101263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8587848522947224670734175 12881772784420837006101263)
          ·
            refine ⟨19322659176631255509151895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12881772784420837006101263 19322659176631255509151895)
            ·
              refine ⟨28983988764946883263727843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19322659176631255509151895 28983988764946883263727843)
              ·
                refine ⟨43475983147420324895591765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28983988764946883263727843 43475983147420324895591765)
                ·
                  refine ⟨63685522188603991546277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 43475983147420324895591765 63685522188603991546277)
                  ·
                    rfl

theorem cell23_1116244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_1116244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116244 prefixEnd_1116244 := by exact prefixLift 1116244
  have htrace : WordTrace (prefixWord ++ tailWord_1116244) baseStart_1116244 baseEnd_1116244 := by
    simpa [prefixWord, tailWord_1116244, baseEnd_1116244] using wordTrace_append hprefix tailTrace_1116244
  have hstable : (prefixWord ++ tailWord_1116244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116244).length < 2 ^ (prefixWord ++ tailWord_1116244).sum := by decide
  have hdescent : baseEnd_1116244 < baseStart_1116244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116261 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 7]
def baseStart_1116261 : Nat := 118140960795 + 1116261 * 2 ^ 59
def prefixEnd_1116261 : Nat := 4983230072969 + 3 ^ 40 * 1116261 * 2
def baseEnd_1116261 : Nat := 63686492096506928600435

theorem tailTrace_1116261 : CollatzResearch.WordTrace tailWord_1116261 prefixEnd_1116261 63686492096506928600435 := by
  unfold tailWord_1116261
  simp only [CollatzResearch.WordTrace]
  refine ⟨40713383408984514046108637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27142255605989676030739091 40713383408984514046108637)
  ·
    refine ⟨15267518778369192767290739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40713383408984514046108637 15267518778369192767290739)
    ·
      refine ⟨22901278167553789150936109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15267518778369192767290739 22901278167553789150936109)
      ·
        refine ⟨8587979312832670931601041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22901278167553789150936109 8587979312832670931601041)
        ·
          refine ⟨6440984484624503198700781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8587979312832670931601041 6440984484624503198700781)
          ·
            refine ⟨2415369181734188699512793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6440984484624503198700781 2415369181734188699512793)
            ·
              refine ⟨1811526886300641524634595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2415369181734188699512793 1811526886300641524634595)
              ·
                refine ⟨2717290329450962286951893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811526886300641524634595 2717290329450962286951893)
                ·
                  refine ⟨63686492096506928600435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2717290329450962286951893 63686492096506928600435)
                  ·
                    rfl

theorem cell23_1116261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_1116261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116261 prefixEnd_1116261 := by exact prefixLift 1116261
  have htrace : WordTrace (prefixWord ++ tailWord_1116261) baseStart_1116261 baseEnd_1116261 := by
    simpa [prefixWord, tailWord_1116261, baseEnd_1116261] using wordTrace_append hprefix tailTrace_1116261
  have hstable : (prefixWord ++ tailWord_1116261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116261).length < 2 ^ (prefixWord ++ tailWord_1116261).sum := by decide
  have hdescent : baseEnd_1116261 < baseStart_1116261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116271 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 3]
def baseStart_1116271 : Nat := 118140960795 + 1116271 * 2 ^ 59
def prefixEnd_1116271 : Nat := 4983230072969 + 3 ^ 40 * 1116271 * 2
def baseEnd_1116271 : Nat := 573183563675107318278869

theorem tailTrace_1116271 : CollatzResearch.WordTrace tailWord_1116271 prefixEnd_1116271 573183563675107318278869 := by
  unfold tailWord_1116271
  simp only [CollatzResearch.WordTrace]
  refine ⟨40713748138948285753972667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27142498759298857169315111 40713748138948285753972667)
  ·
    refine ⟨61070622208422428630959001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40713748138948285753972667 61070622208422428630959001)
    ·
      refine ⟨45802966656316821473219251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61070622208422428630959001 45802966656316821473219251)
      ·
        refine ⟨68704449984475232209828877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45802966656316821473219251 68704449984475232209828877)
        ·
          refine ⟨25764168744178212078685829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68704449984475232209828877 25764168744178212078685829)
          ·
            refine ⟨4830781639533414764753593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25764168744178212078685829 4830781639533414764753593)
            ·
              refine ⟨3623086229650061073565195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4830781639533414764753593 3623086229650061073565195)
              ·
                refine ⟨5434629344475091610347793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623086229650061073565195 5434629344475091610347793)
                ·
                  refine ⟨4075972008356318707760845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5434629344475091610347793 4075972008356318707760845)
                  ·
                    refine ⟨1528489503133619515410317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4075972008356318707760845 1528489503133619515410317)
                    ·
                      refine ⟨573183563675107318278869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1528489503133619515410317 573183563675107318278869)
                      ·
                        rfl

theorem cell23_1116271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_1116271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116271 prefixEnd_1116271 := by exact prefixLift 1116271
  have htrace : WordTrace (prefixWord ++ tailWord_1116271) baseStart_1116271 baseEnd_1116271 := by
    simpa [prefixWord, tailWord_1116271, baseEnd_1116271] using wordTrace_append hprefix tailTrace_1116271
  have hstable : (prefixWord ++ tailWord_1116271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116271).length < 2 ^ (prefixWord ++ tailWord_1116271).sum := by decide
  have hdescent : baseEnd_1116271 < baseStart_1116271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116272 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 2, 2, 2]
def baseStart_1116272 : Nat := 118140960795 + 1116272 * 2 ^ 59
def prefixEnd_1116272 : Nat := 4983230072969 + 3 ^ 40 * 1116272 * 2
def baseEnd_1116272 : Nat := 573184077155761814366365

theorem tailTrace_1116272 : CollatzResearch.WordTrace tailWord_1116272 prefixEnd_1116272 573184077155761814366365 := by
  unfold tailWord_1116272
  simp only [CollatzResearch.WordTrace]
  refine ⟨20356892305972331462379535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27142523074629775283172713 20356892305972331462379535)
  ·
    refine ⟨30535338458958497193569303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20356892305972331462379535 30535338458958497193569303)
    ·
      refine ⟨45803007688437745790353955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30535338458958497193569303 45803007688437745790353955)
      ·
        refine ⟨68704511532656618685530933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45803007688437745790353955 68704511532656618685530933)
        ·
          refine ⟨6441047956186558001768525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68704511532656618685530933 6441047956186558001768525)
          ·
            refine ⟨2415392983569959250663197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6441047956186558001768525 2415392983569959250663197)
            ·
              refine ⟨905772368838734718998699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2415392983569959250663197 905772368838734718998699)
              ·
                refine ⟨1358658553258102078498049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905772368838734718998699 1358658553258102078498049)
                ·
                  refine ⟨1018993914943576558873537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1358658553258102078498049 1018993914943576558873537)
                  ·
                    refine ⟨764245436207682419155153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1018993914943576558873537 764245436207682419155153)
                    ·
                      refine ⟨573184077155761814366365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764245436207682419155153 573184077155761814366365)
                      ·
                        rfl

theorem cell23_1116272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 2, 2].length) (baseStart_1116272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116272 prefixEnd_1116272 := by exact prefixLift 1116272
  have htrace : WordTrace (prefixWord ++ tailWord_1116272) baseStart_1116272 baseEnd_1116272 := by
    simpa [prefixWord, tailWord_1116272, baseEnd_1116272] using wordTrace_append hprefix tailTrace_1116272
  have hstable : (prefixWord ++ tailWord_1116272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116272).length < 2 ^ (prefixWord ++ tailWord_1116272).sum := by decide
  have hdescent : baseEnd_1116272 < baseStart_1116272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116388 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_1116388 : Nat := 118140960795 + 1116388 * 2 ^ 59
def prefixEnd_1116388 : Nat := 4983230072969 + 3 ^ 40 * 1116388 * 2
def baseEnd_1116388 : Nat := 573243640911683360515831

theorem tailTrace_1116388 : CollatzResearch.WordTrace tailWord_1116388 prefixEnd_1116388 573243640911683360515831 := by
  unfold tailWord_1116388
  simp only [CollatzResearch.WordTrace]
  refine ⟨20359007739762207367990909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27145343653016276490654545 20359007739762207367990909)
  ·
    refine ⟨7634627902410827762996591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20359007739762207367990909 7634627902410827762996591)
    ·
      refine ⟨11451941853616241644494887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7634627902410827762996591 11451941853616241644494887)
      ·
        refine ⟨17177912780424362466742331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11451941853616241644494887 17177912780424362466742331)
        ·
          refine ⟨25766869170636543700113497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17177912780424362466742331 25766869170636543700113497)
          ·
            refine ⟨19325151877977407775085123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25766869170636543700113497 19325151877977407775085123)
            ·
              refine ⟨28987727816966111662627685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19325151877977407775085123 28987727816966111662627685)
              ·
                refine ⟨5435198965681145936742691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28987727816966111662627685 5435198965681145936742691)
                ·
                  refine ⟨8152798448521718905114037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5435198965681145936742691 8152798448521718905114037)
                  ·
                    refine ⟨764324854548911147354441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8152798448521718905114037 764324854548911147354441)
                    ·
                      refine ⟨573243640911683360515831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764324854548911147354441 573243640911683360515831)
                      ·
                        rfl

theorem cell23_1116388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_1116388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116388 prefixEnd_1116388 := by exact prefixLift 1116388
  have htrace : WordTrace (prefixWord ++ tailWord_1116388) baseStart_1116388 baseEnd_1116388 := by
    simpa [prefixWord, tailWord_1116388, baseEnd_1116388] using wordTrace_append hprefix tailTrace_1116388
  have hstable : (prefixWord ++ tailWord_1116388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116388).length < 2 ^ (prefixWord ++ tailWord_1116388).sum := by decide
  have hdescent : baseEnd_1116388 < baseStart_1116388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116398 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1116398 : Nat := 118140960795 + 1116398 * 2 ^ 59
def prefixEnd_1116398 : Nat := 4983230072969 + 3 ^ 40 * 1116398 * 2
def baseEnd_1116398 : Nat := 191082925239409440463595

theorem tailTrace_1116398 : CollatzResearch.WordTrace tailWord_1116398 prefixEnd_1116398 191082925239409440463595 := by
  unfold tailWord_1116398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089797526186023305480731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27145586806325457629230565 5089797526186023305480731)
  ·
    refine ⟨7634696289279034958221097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5089797526186023305480731 7634696289279034958221097)
    ·
      refine ⟨5726022216959276218665823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7634696289279034958221097 5726022216959276218665823)
      ·
        refine ⟨8589033325438914327998735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5726022216959276218665823 8589033325438914327998735)
        ·
          refine ⟨12883549988158371491998103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8589033325438914327998735 12883549988158371491998103)
          ·
            refine ⟨19325324982237557237997155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12883549988158371491998103 19325324982237557237997155)
            ·
              refine ⟨28987987473356335856995733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19325324982237557237997155 28987987473356335856995733)
              ·
                refine ⟨1358811912813578243296675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28987987473356335856995733 1358811912813578243296675)
                ·
                  refine ⟨2038217869220367364945013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358811912813578243296675 2038217869220367364945013)
                  ·
                    refine ⟨191082925239409440463595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2038217869220367364945013 191082925239409440463595)
                    ·
                      rfl

theorem cell23_1116398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1116398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116398 prefixEnd_1116398 := by exact prefixLift 1116398
  have htrace : WordTrace (prefixWord ++ tailWord_1116398) baseStart_1116398 baseEnd_1116398 := by
    simpa [prefixWord, tailWord_1116398, baseEnd_1116398] using wordTrace_append hprefix tailTrace_1116398
  have hstable : (prefixWord ++ tailWord_1116398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116398).length < 2 ^ (prefixWord ++ tailWord_1116398).sum := by decide
  have hdescent : baseEnd_1116398 < baseStart_1116398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116412 : List Nat := [2, 2, 2, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_1116412 : Nat := 118140960795 + 1116412 * 2 ^ 59
def prefixEnd_1116412 : Nat := 4983230072969 + 3 ^ 40 * 1116412 * 2
def baseEnd_1116412 : Nat := 573255964447391266615721

theorem tailTrace_1116412 : CollatzResearch.WordTrace tailWord_1116412 prefixEnd_1116412 573255964447391266615721 := by
  unfold tailWord_1116412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20359445415718733417427745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27145927220958311223236993 20359445415718733417427745)
  ·
    refine ⟨15269584061789050063070809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20359445415718733417427745 15269584061789050063070809)
    ·
      refine ⟨11452188046341787547303107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15269584061789050063070809 11452188046341787547303107)
      ·
        refine ⟨17178282069512681320954661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11452188046341787547303107 17178282069512681320954661)
        ·
          refine ⟨3220927888033627747678999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17178282069512681320954661 3220927888033627747678999)
          ·
            refine ⟨4831391832050441621518499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220927888033627747678999 4831391832050441621518499)
            ·
              refine ⟨7247087748075662432277749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831391832050441621518499 7247087748075662432277749)
              ·
                refine ⟨679414476382093353026039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7247087748075662432277749 679414476382093353026039)
                ·
                  refine ⟨1019121714573140029539059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679414476382093353026039 1019121714573140029539059)
                  ·
                    refine ⟨1528682571859710044308589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1019121714573140029539059 1528682571859710044308589)
                    ·
                      refine ⟨573255964447391266615721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1528682571859710044308589 573255964447391266615721)
                      ·
                        rfl

theorem cell23_1116412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_1116412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116412 prefixEnd_1116412 := by exact prefixLift 1116412
  have htrace : WordTrace (prefixWord ++ tailWord_1116412) baseStart_1116412 baseEnd_1116412 := by
    simpa [prefixWord, tailWord_1116412, baseEnd_1116412] using wordTrace_append hprefix tailTrace_1116412
  have hstable : (prefixWord ++ tailWord_1116412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116412).length < 2 ^ (prefixWord ++ tailWord_1116412).sum := by decide
  have hdescent : baseEnd_1116412 < baseStart_1116412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116428 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_1116428 : Nat := 118140960795 + 1116428 * 2 ^ 59
def prefixEnd_1116428 : Nat := 4983230072969 + 3 ^ 40 * 1116428 * 2
def baseEnd_1116428 : Nat := 191088060045954401338549

theorem tailTrace_1116428 : CollatzResearch.WordTrace tailWord_1116428 prefixEnd_1116428 191088060045954401338549 := by
  unfold tailWord_1116428
  simp only [CollatzResearch.WordTrace]
  refine ⟨20359737199689750783718969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27146316266253001044958625 20359737199689750783718969)
  ·
    refine ⟨15269802899767313087789227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20359737199689750783718969 15269802899767313087789227)
    ·
      refine ⟨22904704349650969631683841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15269802899767313087789227 22904704349650969631683841)
      ·
        refine ⟨17178528262238227223762881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22904704349650969631683841 17178528262238227223762881)
        ·
          refine ⟨12883896196678670417822161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17178528262238227223762881 12883896196678670417822161)
          ·
            refine ⟨9662922147509002813366621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12883896196678670417822161 9662922147509002813366621)
            ·
              refine ⟨3623595805315876055012483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9662922147509002813366621 3623595805315876055012483)
              ·
                refine ⟨5435393707973814082518725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623595805315876055012483 5435393707973814082518725)
                ·
                  refine ⟨1019136320245090140472261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5435393707973814082518725 1019136320245090140472261)
                  ·
                    refine ⟨191088060045954401338549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1019136320245090140472261 191088060045954401338549)
                    ·
                      rfl

theorem cell23_1116428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_1116428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116428 prefixEnd_1116428 := by exact prefixLift 1116428
  have htrace : WordTrace (prefixWord ++ tailWord_1116428) baseStart_1116428 baseEnd_1116428 := by
    simpa [prefixWord, tailWord_1116428, baseEnd_1116428] using wordTrace_append hprefix tailTrace_1116428
  have hstable : (prefixWord ++ tailWord_1116428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116428).length < 2 ^ (prefixWord ++ tailWord_1116428).sum := by decide
  have hdescent : baseEnd_1116428 < baseStart_1116428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116431 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_1116431 : Nat := 118140960795 + 1116431 * 2 ^ 59
def prefixEnd_1116431 : Nat := 4983230072969 + 3 ^ 40 * 1116431 * 2
def baseEnd_1116431 : Nat := 573265720579826692278133

theorem tailTrace_1116431 : CollatzResearch.WordTrace tailWord_1116431 prefixEnd_1116431 573265720579826692278133 := by
  unfold tailWord_1116431
  simp only [CollatzResearch.WordTrace]
  refine ⟨40719583818368633079797147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27146389212245755386531431 40719583818368633079797147)
  ·
    refine ⟨61079375727552949619695721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40719583818368633079797147 61079375727552949619695721)
    ·
      refine ⟨45809531795664712214771791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61079375727552949619695721 45809531795664712214771791)
      ·
        refine ⟨68714297693497068322157687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45809531795664712214771791 68714297693497068322157687)
        ·
          refine ⟨103071446540245602483236531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68714297693497068322157687 103071446540245602483236531)
          ·
            refine ⟨154607169810368403724854797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103071446540245602483236531 154607169810368403724854797)
            ·
              refine ⟨57977688678888151396820549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154607169810368403724854797 57977688678888151396820549)
              ·
                refine ⟨10870816627291528386903853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57977688678888151396820549 10870816627291528386903853)
                ·
                  refine ⟨4076556235234323145088945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10870816627291528386903853 4076556235234323145088945)
                  ·
                    refine ⟨3057417176425742358816709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4076556235234323145088945 3057417176425742358816709)
                    ·
                      refine ⟨573265720579826692278133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3057417176425742358816709 573265720579826692278133)
                      ·
                        rfl

theorem cell23_1116431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_1116431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116431 prefixEnd_1116431 := by exact prefixLift 1116431
  have htrace : WordTrace (prefixWord ++ tailWord_1116431) baseStart_1116431 baseEnd_1116431 := by
    simpa [prefixWord, tailWord_1116431, baseEnd_1116431] using wordTrace_append hprefix tailTrace_1116431
  have hstable : (prefixWord ++ tailWord_1116431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116431).length < 2 ^ (prefixWord ++ tailWord_1116431).sum := by decide
  have hdescent : baseEnd_1116431 < baseStart_1116431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116448 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1116448 : Nat := 118140960795 + 1116448 * 2 ^ 59
def prefixEnd_1116448 : Nat := 4983230072969 + 3 ^ 40 * 1116448 * 2
def baseEnd_1116448 : Nat := 573274449750953125765555

theorem tailTrace_1116448 : CollatzResearch.WordTrace tailWord_1116448 prefixEnd_1116448 573274449750953125765555 := by
  unfold tailWord_1116448
  simp only [CollatzResearch.WordTrace]
  refine ⟨20360101929653522491582999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27146802572871363322110665 20360101929653522491582999)
  ·
    refine ⟨30540152894480283737374499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20360101929653522491582999 30540152894480283737374499)
    ·
      refine ⟨45810229341720425606061749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30540152894480283737374499 45810229341720425606061749)
      ·
        refine ⟨4294709000786289900568289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45810229341720425606061749 4294709000786289900568289)
        ·
          refine ⟨3221031750589717425426217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4294709000786289900568289 3221031750589717425426217)
          ·
            refine ⟨2415773812942288069069663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3221031750589717425426217 2415773812942288069069663)
            ·
              refine ⟨3623660719413432103604495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415773812942288069069663 3623660719413432103604495)
              ·
                refine ⟨5435491079120148155406743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623660719413432103604495 5435491079120148155406743)
                ·
                  refine ⟨8153236618680222233110115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5435491079120148155406743 8153236618680222233110115)
                  ·
                    refine ⟨12229854928020333349665173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8153236618680222233110115 12229854928020333349665173)
                    ·
                      refine ⟨573274449750953125765555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12229854928020333349665173 573274449750953125765555)
                      ·
                        rfl

theorem cell23_1116448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1116448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116448 prefixEnd_1116448 := by exact prefixLift 1116448
  have htrace : WordTrace (prefixWord ++ tailWord_1116448) baseStart_1116448 baseEnd_1116448 := by
    simpa [prefixWord, tailWord_1116448, baseEnd_1116448] using wordTrace_append hprefix tailTrace_1116448
  have hstable : (prefixWord ++ tailWord_1116448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116448).length < 2 ^ (prefixWord ++ tailWord_1116448).sum := by decide
  have hdescent : baseEnd_1116448 < baseStart_1116448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116452 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_1116452 : Nat := 118140960795 + 1116452 * 2 ^ 59
def prefixEnd_1116452 : Nat := 4983230072969 + 3 ^ 40 * 1116452 * 2
def baseEnd_1116452 : Nat := 573276503673571110115537

theorem tailTrace_1116452 : CollatzResearch.WordTrace tailWord_1116452 prefixEnd_1116452 573276503673571110115537 := by
  unfold tailWord_1116452
  simp only [CollatzResearch.WordTrace]
  refine ⟨20360174875646276833155805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27146899834195035777541073 20360174875646276833155805)
  ·
    refine ⟨7635065578367353812433427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20360174875646276833155805 7635065578367353812433427)
    ·
      refine ⟨11452598367551030718650141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7635065578367353812433427 11452598367551030718650141)
      ·
        refine ⟨4294724387831636519493803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11452598367551030718650141 4294724387831636519493803)
        ·
          refine ⟨6442086581747454779240705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294724387831636519493803 6442086581747454779240705)
          ·
            refine ⟨4831564936310591084430529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6442086581747454779240705 4831564936310591084430529)
            ·
              refine ⟨3623673702232943313322897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831564936310591084430529 3623673702232943313322897)
              ·
                refine ⟨2717755276674707484992173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3623673702232943313322897 2717755276674707484992173)
                ·
                  refine ⟨1019158228753015306872065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2717755276674707484992173 1019158228753015306872065)
                  ·
                    refine ⟨764368671564761480154049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1019158228753015306872065 764368671564761480154049)
                    ·
                      refine ⟨573276503673571110115537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764368671564761480154049 573276503673571110115537)
                      ·
                        rfl

theorem cell23_1116452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_1116452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116452 prefixEnd_1116452 := by exact prefixLift 1116452
  have htrace : WordTrace (prefixWord ++ tailWord_1116452) baseStart_1116452 baseEnd_1116452 := by
    simpa [prefixWord, tailWord_1116452, baseEnd_1116452] using wordTrace_append hprefix tailTrace_1116452
  have hstable : (prefixWord ++ tailWord_1116452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116452).length < 2 ^ (prefixWord ++ tailWord_1116452).sum := by decide
  have hdescent : baseEnd_1116452 < baseStart_1116452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116512 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 3, 3, 2]
def baseStart_1116512 : Nat := 118140960795 + 1116512 * 2 ^ 59
def prefixEnd_1116512 : Nat := 4983230072969 + 3 ^ 40 * 1116512 * 2
def baseEnd_1116512 : Nat := 573307312512840875365261

theorem tailTrace_1116512 : CollatzResearch.WordTrace tailWord_1116512 prefixEnd_1116512 573307312512840875365261 := by
  unfold tailWord_1116512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20361269065537591956747895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27148358754050122608997193 20361269065537591956747895)
  ·
    refine ⟨30541903598306387935121843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20361269065537591956747895 30541903598306387935121843)
    ·
      refine ⟨45812855397459581902682765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30541903598306387935121843 45812855397459581902682765)
      ·
        refine ⟨17179820774047343213506037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45812855397459581902682765 17179820774047343213506037)
        ·
          refine ⟨1610608197566938426266191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17179820774047343213506037 1610608197566938426266191)
          ·
            refine ⟨2415912296350407639399287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610608197566938426266191 2415912296350407639399287)
            ·
              refine ⟨3623868444525611459098931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415912296350407639399287 3623868444525611459098931)
              ·
                refine ⟨5435802666788417188648397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623868444525611459098931 5435802666788417188648397)
                ·
                  refine ⟨2038426000045656445743149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5435802666788417188648397 2038426000045656445743149)
                  ·
                    refine ⟨764409750017121167153681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038426000045656445743149 764409750017121167153681)
                    ·
                      refine ⟨573307312512840875365261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764409750017121167153681 573307312512840875365261)
                      ·
                        rfl

theorem cell23_1116512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_1116512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116512 prefixEnd_1116512 := by exact prefixLift 1116512
  have htrace : WordTrace (prefixWord ++ tailWord_1116512) baseStart_1116512 baseEnd_1116512 := by
    simpa [prefixWord, tailWord_1116512, baseEnd_1116512] using wordTrace_append hprefix tailTrace_1116512
  have hstable : (prefixWord ++ tailWord_1116512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116512).length < 2 ^ (prefixWord ++ tailWord_1116512).sum := by decide
  have hdescent : baseEnd_1116512 < baseStart_1116512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116528 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_1116528 : Nat := 118140960795 + 1116528 * 2 ^ 59
def prefixEnd_1116528 : Nat := 4983230072969 + 3 ^ 40 * 1116528 * 2
def baseEnd_1116528 : Nat := 573315528203312812765187

theorem tailTrace_1116528 : CollatzResearch.WordTrace tailWord_1116528 prefixEnd_1116528 573315528203312812765187 := by
  unfold tailWord_1116528
  simp only [CollatzResearch.WordTrace]
  refine ⟨20361560849508609323039119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27148747799344812430718825 20361560849508609323039119)
  ·
    refine ⟨30542341274262913984558679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20361560849508609323039119 30542341274262913984558679)
    ·
      refine ⟨45813511911394370976838019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30542341274262913984558679 45813511911394370976838019)
      ·
        refine ⟨68720267867091556465257029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45813511911394370976838019 68720267867091556465257029)
        ·
          refine ⟨12885050225079666837235693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68720267867091556465257029 12885050225079666837235693)
          ·
            refine ⟨4831893834404875063963385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12885050225079666837235693 4831893834404875063963385)
            ·
              refine ⟨3623920375803656297972539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831893834404875063963385 3623920375803656297972539)
              ·
                refine ⟨5435880563705484446958809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623920375803656297972539 5435880563705484446958809)
                ·
                  refine ⟨4076910422779113335219107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5435880563705484446958809 4076910422779113335219107)
                  ·
                    refine ⟨6115365634168670002828661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4076910422779113335219107 6115365634168670002828661)
                    ·
                      refine ⟨573315528203312812765187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6115365634168670002828661 573315528203312812765187)
                      ·
                        rfl

theorem cell23_1116528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_1116528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116528 prefixEnd_1116528 := by exact prefixLift 1116528
  have htrace : WordTrace (prefixWord ++ tailWord_1116528) baseStart_1116528 baseEnd_1116528 := by
    simpa [prefixWord, tailWord_1116528, baseEnd_1116528] using wordTrace_append hprefix tailTrace_1116528
  have hstable : (prefixWord ++ tailWord_1116528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116528).length < 2 ^ (prefixWord ++ tailWord_1116528).sum := by decide
  have hdescent : baseEnd_1116528 < baseStart_1116528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116531 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 9]
def baseStart_1116531 : Nat := 118140960795 + 1116531 * 2 ^ 59
def prefixEnd_1116531 : Nat := 4983230072969 + 3 ^ 40 * 1116531 * 2
def baseEnd_1116531 : Nat := 63701896516141811225297

theorem tailTrace_1116531 : CollatzResearch.WordTrace tailWord_1116531 prefixEnd_1116531 63701896516141811225297 := by
  unfold tailWord_1116531
  simp only [CollatzResearch.WordTrace]
  refine ⟨40723231118006350158437447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27148820745337566772291631 40723231118006350158437447)
  ·
    refine ⟨61084846677009525237656171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40723231118006350158437447 61084846677009525237656171)
    ·
      refine ⟨91627270015514287856484257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61084846677009525237656171 91627270015514287856484257)
      ·
        refine ⟨68720452511635715892363193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91627270015514287856484257 68720452511635715892363193)
        ·
          refine ⟨51540339383726786919272395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68720452511635715892363193 51540339383726786919272395)
          ·
            refine ⟨77310509075590180378908593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51540339383726786919272395 77310509075590180378908593)
            ·
              refine ⟨57982881806692635284181445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77310509075590180378908593 57982881806692635284181445)
              ·
                refine ⟨10871790338754869115784021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57982881806692635284181445 10871790338754869115784021)
                ·
                  refine ⟨63701896516141811225297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10871790338754869115784021 63701896516141811225297)
                  ·
                    rfl

theorem cell23_1116531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 9].length) (baseStart_1116531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116531 prefixEnd_1116531 := by exact prefixLift 1116531
  have htrace : WordTrace (prefixWord ++ tailWord_1116531) baseStart_1116531 baseEnd_1116531 := by
    simpa [prefixWord, tailWord_1116531, baseEnd_1116531] using wordTrace_append hprefix tailTrace_1116531
  have hstable : (prefixWord ++ tailWord_1116531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116531).length < 2 ^ (prefixWord ++ tailWord_1116531).sum := by decide
  have hdescent : baseEnd_1116531 < baseStart_1116531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116545 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1116545 : Nat := 118140960795 + 1116545 * 2 ^ 59
def prefixEnd_1116545 : Nat := 4983230072969 + 3 ^ 40 * 1116545 * 2
def baseEnd_1116545 : Nat := 573324257374439246252609

theorem tailTrace_1116545 : CollatzResearch.WordTrace tailWord_1116545 prefixEnd_1116545 573324257374439246252609 := by
  unfold tailWord_1116545
  simp only [CollatzResearch.WordTrace]
  refine ⟨40723741739955630549447089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27149161159970420366298059 40723741739955630549447089)
  ·
    refine ⟨30542806304966722912085317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40723741739955630549447089 30542806304966722912085317)
    ·
      refine ⟨5726776182181260546015997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30542806304966722912085317 5726776182181260546015997)
      ·
        refine ⟨2147541068317972704755999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5726776182181260546015997 2147541068317972704755999)
        ·
          refine ⟨3221311602476959057133999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147541068317972704755999 3221311602476959057133999)
          ·
            refine ⟨4831967403715438585700999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221311602476959057133999 4831967403715438585700999)
            ·
              refine ⟨7247951105573157878551499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831967403715438585700999 7247951105573157878551499)
              ·
                refine ⟨10871926658359736817827249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7247951105573157878551499 10871926658359736817827249)
                ·
                  refine ⟨8153944993769802613370437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10871926658359736817827249 8153944993769802613370437)
                  ·
                    refine ⟨1528864686331837990006957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8153944993769802613370437 1528864686331837990006957)
                    ·
                      refine ⟨573324257374439246252609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1528864686331837990006957 573324257374439246252609)
                      ·
                        rfl

theorem cell23_1116545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1116545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116545 prefixEnd_1116545 := by exact prefixLift 1116545
  have htrace : WordTrace (prefixWord ++ tailWord_1116545) baseStart_1116545 baseEnd_1116545 := by
    simpa [prefixWord, tailWord_1116545, baseEnd_1116545] using wordTrace_append hprefix tailTrace_1116545
  have hstable : (prefixWord ++ tailWord_1116545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116545).length < 2 ^ (prefixWord ++ tailWord_1116545).sum := by decide
  have hdescent : baseEnd_1116545 < baseStart_1116545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116548 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 7]
def baseStart_1116548 : Nat := 118140960795 + 1116548 * 2 ^ 59
def prefixEnd_1116548 : Nat := 4983230072969 + 3 ^ 40 * 1116548 * 2
def baseEnd_1116548 : Nat := 63702866424044748279455

theorem tailTrace_1116548 : CollatzResearch.WordTrace tailWord_1116548 prefixEnd_1116548 63702866424044748279455 := by
  unfold tailWord_1116548
  simp only [CollatzResearch.WordTrace]
  refine ⟨20361925579472381030903149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27149234105963174707870865 20361925579472381030903149)
  ·
    refine ⟨7635722092302142886588681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20361925579472381030903149 7635722092302142886588681)
    ·
      refine ⟨5726791569226607164941511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7635722092302142886588681 5726791569226607164941511)
      ·
        refine ⟨8590187353839910747412267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5726791569226607164941511 8590187353839910747412267)
        ·
          refine ⟨12885281030759866121118401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8590187353839910747412267 12885281030759866121118401)
          ·
            refine ⟨9663960773069899590838801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12885281030759866121118401 9663960773069899590838801)
            ·
              refine ⟨7247970579802424693129101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9663960773069899590838801 7247970579802424693129101)
              ·
                refine ⟨2717988967425909259923413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7247970579802424693129101 2717988967425909259923413)
                ·
                  refine ⟨63702866424044748279455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2717988967425909259923413 63702866424044748279455)
                  ·
                    rfl

theorem cell23_1116548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_1116548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116548 prefixEnd_1116548 := by exact prefixLift 1116548
  have htrace : WordTrace (prefixWord ++ tailWord_1116548) baseStart_1116548 baseEnd_1116548 := by
    simpa [prefixWord, tailWord_1116548, baseEnd_1116548] using wordTrace_append hprefix tailTrace_1116548
  have hstable : (prefixWord ++ tailWord_1116548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116548).length < 2 ^ (prefixWord ++ tailWord_1116548).sum := by decide
  have hdescent : baseEnd_1116548 < baseStart_1116548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116659 : List Nat := [1, 1, 1, 2, 2, 2, 7, 2, 1, 4]
def baseStart_1116659 : Nat := 118140960795 + 1116659 * 2 ^ 59
def prefixEnd_1116659 : Nat := 4983230072969 + 3 ^ 40 * 1116659 * 2
def baseEnd_1116659 : Nat := 191127598056350600075695

theorem tailTrace_1116659 : CollatzResearch.WordTrace tailWord_1116659 prefixEnd_1116659 191127598056350600075695 := by
  unfold tailWord_1116659
  simp only [CollatzResearch.WordTrace]
  refine ⟨40727899661542628019097031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27151933107695085346064687 40727899661542628019097031)
  ·
    refine ⟨61091849492313942028645547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40727899661542628019097031 61091849492313942028645547)
    ·
      refine ⟨91637774238470913042968321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61091849492313942028645547 91637774238470913042968321)
      ·
        refine ⟨68728330678853184782226241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91637774238470913042968321 68728330678853184782226241)
        ·
          refine ⟨51546248009139888586669681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68728330678853184782226241 51546248009139888586669681)
          ·
            refine ⟨38659686006854916440002261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51546248009139888586669681 38659686006854916440002261)
            ·
              refine ⟨906086390785662104062553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 38659686006854916440002261 906086390785662104062553)
              ·
                refine ⟨679564793089246578046915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906086390785662104062553 679564793089246578046915)
                ·
                  refine ⟨1019347189633869867070373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679564793089246578046915 1019347189633869867070373)
                  ·
                    refine ⟨191127598056350600075695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1019347189633869867070373 191127598056350600075695)
                    ·
                      rfl

theorem cell23_1116659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 4].length) (baseStart_1116659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116659 prefixEnd_1116659 := by exact prefixLift 1116659
  have htrace : WordTrace (prefixWord ++ tailWord_1116659) baseStart_1116659 baseEnd_1116659 := by
    simpa [prefixWord, tailWord_1116659, baseEnd_1116659] using wordTrace_append hprefix tailTrace_1116659
  have hstable : (prefixWord ++ tailWord_1116659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116659).length < 2 ^ (prefixWord ++ tailWord_1116659).sum := by decide
  have hdescent : baseEnd_1116659 < baseStart_1116659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116668 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_1116668 : Nat := 118140960795 + 1116668 * 2 ^ 59
def prefixEnd_1116668 : Nat := 4983230072969 + 3 ^ 40 * 1116668 * 2
def baseEnd_1116668 : Nat := 191129138498314088338181

theorem tailTrace_1116668 : CollatzResearch.WordTrace tailWord_1116668 prefixEnd_1116668 191129138498314088338181 := by
  unfold tailWord_1116668
  simp only [CollatzResearch.WordTrace]
  refine ⟨20364113959255011278087329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27152151945673348370783105 20364113959255011278087329)
  ·
    refine ⟨15273085469441258458565497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20364113959255011278087329 15273085469441258458565497)
    ·
      refine ⟨11454814102080943843924123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15273085469441258458565497 11454814102080943843924123)
      ·
        refine ⟨17182221153121415765886185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11454814102080943843924123 17182221153121415765886185)
        ·
          refine ⟨12886665864841061824414639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17182221153121415765886185 12886665864841061824414639)
          ·
            refine ⟨19329998797261592736621959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12886665864841061824414639 19329998797261592736621959)
            ·
              refine ⟨28994998195892389104932939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19329998797261592736621959 28994998195892389104932939)
              ·
                refine ⟨43492497293838583657399409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28994998195892389104932939 43492497293838583657399409)
                ·
                  refine ⟨32619372970378937743049557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43492497293838583657399409 32619372970378937743049557)
                  ·
                    refine ⟨191129138498314088338181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 32619372970378937743049557 191129138498314088338181)
                    ·
                      rfl

theorem cell23_1116668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_1116668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116668 prefixEnd_1116668 := by exact prefixLift 1116668
  have htrace : WordTrace (prefixWord ++ tailWord_1116668) baseStart_1116668 baseEnd_1116668 := by
    simpa [prefixWord, tailWord_1116668, baseEnd_1116668] using wordTrace_append hprefix tailTrace_1116668
  have hstable : (prefixWord ++ tailWord_1116668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116668).length < 2 ^ (prefixWord ++ tailWord_1116668).sum := by decide
  have hdescent : baseEnd_1116668 < baseStart_1116668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116682 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1116682 : Nat := 118140960795 + 1116682 * 2 ^ 59
def prefixEnd_1116682 : Nat := 4983230072969 + 3 ^ 40 * 1116682 * 2
def baseEnd_1116682 : Nat := 573394604224105210239479

theorem tailTrace_1116682 : CollatzResearch.WordTrace tailWord_1116682 prefixEnd_1116682 573394604224105210239479 := by
  unfold tailWord_1116682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10182184635114825736796075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27152492360306201964789533 10182184635114825736796075)
  ·
    refine ⟨15273276952672238605194113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10182184635114825736796075 15273276952672238605194113)
    ·
      refine ⟨11454957714504178953895585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15273276952672238605194113 11454957714504178953895585)
      ·
        refine ⟨8591218285878134215421689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11454957714504178953895585 8591218285878134215421689)
        ·
          refine ⟨6443413714408600661566267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8591218285878134215421689 6443413714408600661566267)
          ·
            refine ⟨9665120571612900992349401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443413714408600661566267 9665120571612900992349401)
            ·
              refine ⟨7248840428709675744262051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9665120571612900992349401 7248840428709675744262051)
              ·
                refine ⟨10873260643064513616393077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7248840428709675744262051 10873260643064513616393077)
                ·
                  refine ⟨1019368185287298151536851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10873260643064513616393077 1019368185287298151536851)
                  ·
                    refine ⟨1529052277930947227305277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1019368185287298151536851 1529052277930947227305277)
                    ·
                      refine ⟨573394604224105210239479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1529052277930947227305277 573394604224105210239479)
                      ·
                        rfl

theorem cell23_1116682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1116682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116682 prefixEnd_1116682 := by exact prefixLift 1116682
  have htrace : WordTrace (prefixWord ++ tailWord_1116682) baseStart_1116682 baseEnd_1116682 := by
    simpa [prefixWord, tailWord_1116682, baseEnd_1116682] using wordTrace_append hprefix tailTrace_1116682
  have hstable : (prefixWord ++ tailWord_1116682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116682).length < 2 ^ (prefixWord ++ tailWord_1116682).sum := by decide
  have hdescent : baseEnd_1116682 < baseStart_1116682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116715 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 4, 4]
def baseStart_1116715 : Nat := 118140960795 + 1116715 * 2 ^ 59
def prefixEnd_1116715 : Nat := 4983230072969 + 3 ^ 40 * 1116715 * 2
def baseEnd_1116715 : Nat := 191137183028567860375609

theorem tailTrace_1116715 : CollatzResearch.WordTrace tailWord_1116715 prefixEnd_1116715 191137183028567860375609 := by
  unfold tailWord_1116715
  simp only [CollatzResearch.WordTrace]
  refine ⟨40729942149339749583135599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27153294766226499722090399 40729942149339749583135599)
  ·
    refine ⟨61094913224009624374703399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40729942149339749583135599 61094913224009624374703399)
    ·
      refine ⟨91642369836014436562055099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61094913224009624374703399 91642369836014436562055099)
      ·
        refine ⟨137463554754021654843082649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91642369836014436562055099 137463554754021654843082649)
        ·
          refine ⟨103097666065516241132311987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137463554754021654843082649 103097666065516241132311987)
          ·
            refine ⟨154646499098274361698467981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103097666065516241132311987 154646499098274361698467981)
            ·
              refine ⟨57992437161852885636925493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154646499098274361698467981 57992437161852885636925493)
              ·
                refine ⟨5436790983923708028461765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57992437161852885636925493 5436790983923708028461765)
                ·
                  refine ⟨1019398309485695255336581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5436790983923708028461765 1019398309485695255336581)
                  ·
                    refine ⟨191137183028567860375609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1019398309485695255336581 191137183028567860375609)
                    ·
                      rfl

theorem cell23_1116715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 4].length) (baseStart_1116715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116715 prefixEnd_1116715 := by exact prefixLift 1116715
  have htrace : WordTrace (prefixWord ++ tailWord_1116715) baseStart_1116715 baseEnd_1116715 := by
    simpa [prefixWord, tailWord_1116715, baseEnd_1116715] using wordTrace_append hprefix tailTrace_1116715
  have hstable : (prefixWord ++ tailWord_1116715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116715).length < 2 ^ (prefixWord ++ tailWord_1116715).sum := by decide
  have hdescent : baseEnd_1116715 < baseStart_1116715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116725 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1116725 : Nat := 118140960795 + 1116725 * 2 ^ 59
def prefixEnd_1116725 : Nat := 4983230072969 + 3 ^ 40 * 1116725 * 2
def baseEnd_1116725 : Nat := 573416683892248542001781

theorem tailTrace_1116725 : CollatzResearch.WordTrace tailWord_1116725 prefixEnd_1116725 573416683892248542001781 := by
  unfold tailWord_1116725
  simp only [CollatzResearch.WordTrace]
  refine ⟨40730306879303521290999629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27153537919535680860666419 40730306879303521290999629)
  ·
    refine ⟨15273865079738820484124861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40730306879303521290999629 15273865079738820484124861)
    ·
      refine ⟨5727699404902057681546823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15273865079738820484124861 5727699404902057681546823)
      ·
        refine ⟨8591549107353086522320235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5727699404902057681546823 8591549107353086522320235)
        ·
          refine ⟨12887323661029629783480353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8591549107353086522320235 12887323661029629783480353)
          ·
            refine ⟨9665492745772222337610265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12887323661029629783480353 9665492745772222337610265)
            ·
              refine ⟨7249119559329166753207699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9665492745772222337610265 7249119559329166753207699)
              ·
                refine ⟨10873679338993750129811549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7249119559329166753207699 10873679338993750129811549)
                ·
                  refine ⟨4077629752122656298679331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10873679338993750129811549 4077629752122656298679331)
                  ·
                    refine ⟨6116444628183984448018997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077629752122656298679331 6116444628183984448018997)
                    ·
                      refine ⟨573416683892248542001781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6116444628183984448018997 573416683892248542001781)
                      ·
                        rfl

theorem cell23_1116725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1116725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116725 prefixEnd_1116725 := by exact prefixLift 1116725
  have htrace : WordTrace (prefixWord ++ tailWord_1116725) baseStart_1116725 baseEnd_1116725 := by
    simpa [prefixWord, tailWord_1116725, baseEnd_1116725] using wordTrace_append hprefix tailTrace_1116725
  have hstable : (prefixWord ++ tailWord_1116725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116725).length < 2 ^ (prefixWord ++ tailWord_1116725).sum := by decide
  have hdescent : baseEnd_1116725 < baseStart_1116725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116732 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_1116732 : Nat := 118140960795 + 1116732 * 2 ^ 59
def prefixEnd_1116732 : Nat := 4983230072969 + 3 ^ 40 * 1116732 * 2
def baseEnd_1116732 : Nat := 191140092752276671538083

theorem tailTrace_1116732 : CollatzResearch.WordTrace tailWord_1116732 prefixEnd_1116732 191140092752276671538083 := by
  unfold tailWord_1116732
  simp only [CollatzResearch.WordTrace]
  refine ⟨20365281095139080743252225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27153708126852107657669633 20365281095139080743252225)
  ·
    refine ⟨15273960821354310557439169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20365281095139080743252225 15273960821354310557439169)
    ·
      refine ⟨11455470616015732918079377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15273960821354310557439169 11455470616015732918079377)
      ·
        refine ⟨8591602962011799688559533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11455470616015732918079377 8591602962011799688559533)
        ·
          refine ⟨3221851110754424883209825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8591602962011799688559533 3221851110754424883209825)
          ·
            refine ⟨2416388333065818662407369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3221851110754424883209825 2416388333065818662407369)
            ·
              refine ⟨1812291249799363996805527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2416388333065818662407369 1812291249799363996805527)
              ·
                refine ⟨2718436874699045995208291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812291249799363996805527 2718436874699045995208291)
                ·
                  refine ⟨4077655312048568992812437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718436874699045995208291 4077655312048568992812437)
                  ·
                    refine ⟨191140092752276671538083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4077655312048568992812437 191140092752276671538083)
                    ·
                      rfl

theorem cell23_1116732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_1116732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116732 prefixEnd_1116732 := by exact prefixLift 1116732
  have htrace : WordTrace (prefixWord ++ tailWord_1116732) baseStart_1116732 baseEnd_1116732 := by
    simpa [prefixWord, tailWord_1116732, baseEnd_1116732] using wordTrace_append hprefix tailTrace_1116732
  have hstable : (prefixWord ++ tailWord_1116732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116732).length < 2 ^ (prefixWord ++ tailWord_1116732).sum := by decide
  have hdescent : baseEnd_1116732 < baseStart_1116732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116756 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_1116756 : Nat := 118140960795 + 1116756 * 2 ^ 59
def prefixEnd_1116756 : Nat := 4983230072969 + 3 ^ 40 * 1116756 * 2
def baseEnd_1116756 : Nat := 573432601792537920714139

theorem tailTrace_1116756 : CollatzResearch.WordTrace tailWord_1116756 prefixEnd_1116756 573432601792537920714139 := by
  unfold tailWord_1116756
  simp only [CollatzResearch.WordTrace]
  refine ⟨20365718771095606792689061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27154291694794142390252081 20365718771095606792689061)
  ·
    refine ⟨3818572269580426273629199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20365718771095606792689061 3818572269580426273629199)
    ·
      refine ⟨5727858404370639410443799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3818572269580426273629199 5727858404370639410443799)
      ·
        refine ⟨8591787606555959115665699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5727858404370639410443799 8591787606555959115665699)
        ·
          refine ⟨12887681409833938673498549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8591787606555959115665699 12887681409833938673498549)
          ·
            refine ⟨1208220132171931750640489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12887681409833938673498549 1208220132171931750640489)
            ·
              refine ⟨906165099128948812980367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208220132171931750640489 906165099128948812980367)
              ·
                refine ⟨1359247648693423219470551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906165099128948812980367 1359247648693423219470551)
                ·
                  refine ⟨2038871473040134829205827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359247648693423219470551 2038871473040134829205827)
                  ·
                    refine ⟨3058307209560202243808741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2038871473040134829205827 3058307209560202243808741)
                    ·
                      refine ⟨573432601792537920714139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3058307209560202243808741 573432601792537920714139)
                      ·
                        rfl

theorem cell23_1116756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_1116756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116756 prefixEnd_1116756 := by exact prefixLift 1116756
  have htrace : WordTrace (prefixWord ++ tailWord_1116756) baseStart_1116756 baseEnd_1116756 := by
    simpa [prefixWord, tailWord_1116756, baseEnd_1116756] using wordTrace_append hprefix tailTrace_1116756
  have hstable : (prefixWord ++ tailWord_1116756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116756).length < 2 ^ (prefixWord ++ tailWord_1116756).sum := by decide
  have hdescent : baseEnd_1116756 < baseStart_1116756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116786 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_1116786 : Nat := 118140960795 + 1116786 * 2 ^ 59
def prefixEnd_1116786 : Nat := 4983230072969 + 3 ^ 40 * 1116786 * 2
def baseEnd_1116786 : Nat := 573448006212172803339001

theorem tailTrace_1116786 : CollatzResearch.WordTrace tailWord_1116786 prefixEnd_1116786 573448006212172803339001 := by
  unfold tailWord_1116786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10183132933020632177242553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27155021154721685805980141 10183132933020632177242553)
  ·
    refine ⟨7637349699765474132931915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10183132933020632177242553 7637349699765474132931915)
    ·
      refine ⟨11456024549648211199397873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7637349699765474132931915 11456024549648211199397873)
      ·
        refine ⟨8592018412236158399548405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11456024549648211199397873 8592018412236158399548405)
        ·
          refine ⟨805501726147139849957663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8592018412236158399548405 805501726147139849957663)
          ·
            refine ⟨1208252589220709774936495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805501726147139849957663 1208252589220709774936495)
            ·
              refine ⟨1812378883831064662404743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208252589220709774936495 1812378883831064662404743)
              ·
                refine ⟨2718568325746596993607115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812378883831064662404743 2718568325746596993607115)
                ·
                  refine ⟨4077852488619895490410673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718568325746596993607115 4077852488619895490410673)
                  ·
                    refine ⟨3058389366464921617808005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4077852488619895490410673 3058389366464921617808005)
                    ·
                      refine ⟨573448006212172803339001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3058389366464921617808005 573448006212172803339001)
                      ·
                        rfl

theorem cell23_1116786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_1116786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116786 prefixEnd_1116786 := by exact prefixLift 1116786
  have htrace : WordTrace (prefixWord ++ tailWord_1116786) baseStart_1116786 baseEnd_1116786 := by
    simpa [prefixWord, tailWord_1116786, baseEnd_1116786] using wordTrace_append hprefix tailTrace_1116786
  have hstable : (prefixWord ++ tailWord_1116786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116786).length < 2 ^ (prefixWord ++ tailWord_1116786).sum := by decide
  have hdescent : baseEnd_1116786 < baseStart_1116786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116815 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_1116815 : Nat := 118140960795 + 1116815 * 2 ^ 59
def prefixEnd_1116815 : Nat := 4983230072969 + 3 ^ 40 * 1116815 * 2
def baseEnd_1116815 : Nat := 573462897151153189876367

theorem tailTrace_1116815 : CollatzResearch.WordTrace tailWord_1116815 prefixEnd_1116815 573462897151153189876367 := by
  unfold tailWord_1116815
  simp only [CollatzResearch.WordTrace]
  refine ⟨40733589448977466661775899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27155726299318311107850599 40733589448977466661775899)
  ·
    refine ⟨61100384173466199992663849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40733589448977466661775899 61100384173466199992663849)
    ·
      refine ⟨45825288130099649994497887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61100384173466199992663849 45825288130099649994497887)
      ·
        refine ⟨68737932195149474991746831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45825288130099649994497887 68737932195149474991746831)
        ·
          refine ⟨103106898292724212487620247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68737932195149474991746831 103106898292724212487620247)
          ·
            refine ⟨154660347439086318731430371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103106898292724212487620247 154660347439086318731430371)
            ·
              refine ⟨231990521158629478097145557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154660347439086318731430371 231990521158629478097145557)
              ·
                refine ⟨5437277839655378392901849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 231990521158629478097145557 5437277839655378392901849)
                ·
                  refine ⟨4077958379741533794676387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5437277839655378392901849 4077958379741533794676387)
                  ·
                    refine ⟨6116937569612300692014581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077958379741533794676387 6116937569612300692014581)
                    ·
                      refine ⟨573462897151153189876367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6116937569612300692014581 573462897151153189876367)
                      ·
                        rfl

theorem cell23_1116815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_1116815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116815 prefixEnd_1116815 := by exact prefixLift 1116815
  have htrace : WordTrace (prefixWord ++ tailWord_1116815) baseStart_1116815 baseEnd_1116815 := by
    simpa [prefixWord, tailWord_1116815, baseEnd_1116815] using wordTrace_append hprefix tailTrace_1116815
  have hstable : (prefixWord ++ tailWord_1116815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116815).length < 2 ^ (prefixWord ++ tailWord_1116815).sum := by decide
  have hdescent : baseEnd_1116815 < baseStart_1116815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116835 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 7]
def baseStart_1116835 : Nat := 118140960795 + 1116835 * 2 ^ 59
def prefixEnd_1116835 : Nat := 4983230072969 + 3 ^ 40 * 1116835 * 2
def baseEnd_1116835 : Nat := 63719240751582567958475

theorem tailTrace_1116835 : CollatzResearch.WordTrace tailWord_1116835 prefixEnd_1116835 63719240751582567958475 := by
  unfold tailWord_1116835
  simp only [CollatzResearch.WordTrace]
  refine ⟨40734318908905010077503959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27156212605936673385002639 40734318908905010077503959)
  ·
    refine ⟨61101478363357515116255939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40734318908905010077503959 61101478363357515116255939)
    ·
      refine ⟨91652217545036272674383909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61101478363357515116255939 91652217545036272674383909)
      ·
        refine ⟨17184790789694301126446983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91652217545036272674383909 17184790789694301126446983)
        ·
          refine ⟨25777186184541451689670475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17184790789694301126446983 25777186184541451689670475)
          ·
            refine ⟨38665779276812177534505713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25777186184541451689670475 38665779276812177534505713)
            ·
              refine ⟨28999334457609133150879285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38665779276812177534505713 28999334457609133150879285)
              ·
                refine ⟨2718687605400856232894933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28999334457609133150879285 2718687605400856232894933)
                ·
                  refine ⟨63719240751582567958475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2718687605400856232894933 63719240751582567958475)
                  ·
                    rfl

theorem cell23_1116835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 7].length) (baseStart_1116835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116835 prefixEnd_1116835 := by exact prefixLift 1116835
  have htrace : WordTrace (prefixWord ++ tailWord_1116835) baseStart_1116835 baseEnd_1116835 := by
    simpa [prefixWord, tailWord_1116835, baseEnd_1116835] using wordTrace_append hprefix tailTrace_1116835
  have hstable : (prefixWord ++ tailWord_1116835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116835).length < 2 ^ (prefixWord ++ tailWord_1116835).sum := by decide
  have hdescent : baseEnd_1116835 < baseStart_1116835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116932 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1116932 : Nat := 118140960795 + 1116932 * 2 ^ 59
def prefixEnd_1116932 : Nat := 4983230072969 + 3 ^ 40 * 1116932 * 2
def baseEnd_1116932 : Nat := 573522974387729232113329

theorem tailTrace_1116932 : CollatzResearch.WordTrace tailWord_1116932 prefixEnd_1116932 573522974387729232113329 := by
  unfold tailWord_1116932
  simp only [CollatzResearch.WordTrace]
  refine ⟨20368928394776797821892525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27158571193035730429190033 20368928394776797821892525)
  ·
    refine ⟨7638348148041299183209697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20368928394776797821892525 7638348148041299183209697)
    ·
      refine ⟨5728761111030974387407273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7638348148041299183209697 5728761111030974387407273)
      ·
        refine ⟨4296570833273230790555455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5728761111030974387407273 4296570833273230790555455)
        ·
          refine ⟨6444856249909846185833183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4296570833273230790555455 6444856249909846185833183)
          ·
            refine ⟨9667284374864769278749775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6444856249909846185833183 9667284374864769278749775)
            ·
              refine ⟨14500926562297153918124663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9667284374864769278749775 14500926562297153918124663)
              ·
                refine ⟨21751389843445730877186995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14500926562297153918124663 21751389843445730877186995)
                ·
                  refine ⟨32627084765168596315780493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21751389843445730877186995 32627084765168596315780493)
                  ·
                    refine ⟨12235156786938223618417685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32627084765168596315780493 12235156786938223618417685)
                    ·
                      refine ⟨573522974387729232113329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12235156786938223618417685 573522974387729232113329)
                      ·
                        rfl

theorem cell23_1116932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1116932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1116932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1116932 prefixEnd_1116932 := by exact prefixLift 1116932
  have htrace : WordTrace (prefixWord ++ tailWord_1116932) baseStart_1116932 baseEnd_1116932 := by
    simpa [prefixWord, tailWord_1116932, baseEnd_1116932] using wordTrace_append hprefix tailTrace_1116932
  have hstable : (prefixWord ++ tailWord_1116932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116932).length < 2 ^ (prefixWord ++ tailWord_1116932).sum := by decide
  have hdescent : baseEnd_1116932 < baseStart_1116932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117002 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1117002 : Nat := 118140960795 + 1117002 * 2 ^ 59
def prefixEnd_1117002 : Nat := 4983230072969 + 3 ^ 40 * 1117002 * 2
def baseEnd_1117002 : Nat := 191186306011181319412669

theorem tailTrace_1117002 : CollatzResearch.WordTrace tailWord_1117002 prefixEnd_1117002 191186306011181319412669 := by
  unfold tailWord_1117002
  simp only [CollatzResearch.WordTrace]
  refine ⟨10185102474824999399708315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27160273266199998399222173 10185102474824999399708315)
  ·
    refine ⟨15277653712237499099562473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10185102474824999399708315 15277653712237499099562473)
    ·
      refine ⟨11458240284178124324671855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15277653712237499099562473 11458240284178124324671855)
      ·
        refine ⟨17187360426267186487007783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11458240284178124324671855 17187360426267186487007783)
        ·
          refine ⟨25781040639400779730511675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17187360426267186487007783 25781040639400779730511675)
          ·
            refine ⟨38671560959101169595767513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25781040639400779730511675 38671560959101169595767513)
            ·
              refine ⟨29003670719325877196825635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38671560959101169595767513 29003670719325877196825635)
              ·
                refine ⟨43505506078988815795238453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29003670719325877196825635 43505506078988815795238453)
                ·
                  refine ⟨4078641194905201480803605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43505506078988815795238453 4078641194905201480803605)
                  ·
                    refine ⟨191186306011181319412669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4078641194905201480803605 191186306011181319412669)
                    ·
                      rfl

theorem cell23_1117002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1117002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117002 prefixEnd_1117002 := by exact prefixLift 1117002
  have htrace : WordTrace (prefixWord ++ tailWord_1117002) baseStart_1117002 baseEnd_1117002 := by
    simpa [prefixWord, tailWord_1117002, baseEnd_1117002] using wordTrace_append hprefix tailTrace_1117002
  have hstable : (prefixWord ++ tailWord_1117002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117002).length < 2 ^ (prefixWord ++ tailWord_1117002).sum := by decide
  have hdescent : baseEnd_1117002 < baseStart_1117002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117059 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 3]
def baseStart_1117059 : Nat := 118140960795 + 1117059 * 2 ^ 59
def prefixEnd_1117059 : Nat := 4983230072969 + 3 ^ 40 * 1117059 * 2
def baseEnd_1117059 : Nat := 573588186430850235225245

theorem tailTrace_1117059 : CollatzResearch.WordTrace tailWord_1117059 prefixEnd_1117059 573588186430850235225245 := by
  unfold tailWord_1117059
  simp only [CollatzResearch.WordTrace]
  refine ⟨40742488860093496333658231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27161659240062330889105487 40742488860093496333658231)
  ·
    refine ⟨61113733290140244500487347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40742488860093496333658231 61113733290140244500487347)
    ·
      refine ⟨91670599935210366750731021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61113733290140244500487347 91670599935210366750731021)
      ·
        refine ⟨34376474975703887531524133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91670599935210366750731021 34376474975703887531524133)
        ·
          refine ⟨6445589057944478912160775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34376474975703887531524133 6445589057944478912160775)
          ·
            refine ⟨9668383586916718368241163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6445589057944478912160775 9668383586916718368241163)
            ·
              refine ⟨14502575380375077552361745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9668383586916718368241163 14502575380375077552361745)
              ·
                refine ⟨10876931535281308164271309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14502575380375077552361745 10876931535281308164271309)
                ·
                  refine ⟨4078849325730490561601741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10876931535281308164271309 4078849325730490561601741)
                  ·
                    refine ⟨1529568497148933960600653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4078849325730490561601741 1529568497148933960600653)
                    ·
                      refine ⟨573588186430850235225245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1529568497148933960600653 573588186430850235225245)
                      ·
                        rfl

theorem cell23_1117059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_1117059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117059 prefixEnd_1117059 := by exact prefixLift 1117059
  have htrace : WordTrace (prefixWord ++ tailWord_1117059) baseStart_1117059 baseEnd_1117059 := by
    simpa [prefixWord, tailWord_1117059, baseEnd_1117059] using wordTrace_append hprefix tailTrace_1117059
  have hstable : (prefixWord ++ tailWord_1117059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117059).length < 2 ^ (prefixWord ++ tailWord_1117059).sum := by decide
  have hdescent : baseEnd_1117059 < baseStart_1117059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117066 : List Nat := [3, 1, 2, 4, 1, 3, 1, 8]
def baseStart_1117066 : Nat := 118140960795 + 1117066 * 2 ^ 59
def prefixEnd_1117066 : Nat := 4983230072969 + 3 ^ 40 * 1117066 * 2
def baseEnd_1117066 : Nat := 21244140029460433623619

theorem tailTrace_1117066 : CollatzResearch.WordTrace tailWord_1117066 prefixEnd_1117066 21244140029460433623619 := by
  unfold tailWord_1117066
  simp only [CollatzResearch.WordTrace]
  refine ⟨10185686042767034132290763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27161829447378757686108701 10185686042767034132290763)
  ·
    refine ⟨15278529064150551198436145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10185686042767034132290763 15278529064150551198436145)
    ·
      refine ⟨11458896798112913398827109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15278529064150551198436145 11458896798112913398827109)
      ·
        refine ⟨2148543149646171262280083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11458896798112913398827109 2148543149646171262280083)
        ·
          refine ⟨3222814724469256893420125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148543149646171262280083 3222814724469256893420125)
          ·
            refine ⟨1208555521675971335032547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3222814724469256893420125 1208555521675971335032547)
            ·
              refine ⟨1812833282513957002548821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208555521675971335032547 1812833282513957002548821)
              ·
                refine ⟨21244140029460433623619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1812833282513957002548821 21244140029460433623619)
                ·
                  rfl

theorem cell23_1117066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 8].length) (baseStart_1117066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117066 prefixEnd_1117066 := by exact prefixLift 1117066
  have htrace : WordTrace (prefixWord ++ tailWord_1117066) baseStart_1117066 baseEnd_1117066 := by
    simpa [prefixWord, tailWord_1117066, baseEnd_1117066] using wordTrace_append hprefix tailTrace_1117066
  have hstable : (prefixWord ++ tailWord_1117066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117066).length < 2 ^ (prefixWord ++ tailWord_1117066).sum := by decide
  have hdescent : baseEnd_1117066 < baseStart_1117066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117109 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1117109 : Nat := 118140960795 + 1117109 * 2 ^ 59
def prefixEnd_1117109 : Nat := 4983230072969 + 3 ^ 40 * 1117109 * 2
def baseEnd_1117109 : Nat := 191204620154525013200005

theorem tailTrace_1117109 : CollatzResearch.WordTrace tailWord_1117109 prefixEnd_1117109 191204620154525013200005 := by
  unfold tailWord_1117109
  simp only [CollatzResearch.WordTrace]
  refine ⟨40744312509912354872978381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27162875006608236581985587 40744312509912354872978381)
  ·
    refine ⟨15279117191217133077366893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40744312509912354872978381 15279117191217133077366893)
    ·
      refine ⟨5729668946706424904012585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15279117191217133077366893 5729668946706424904012585)
      ·
        refine ⟨4297251710029818678009439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5729668946706424904012585 4297251710029818678009439)
        ·
          refine ⟨6445877565044728017014159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4297251710029818678009439 6445877565044728017014159)
          ·
            refine ⟨9668816347567092025521239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6445877565044728017014159 9668816347567092025521239)
            ·
              refine ⟨14503224521350638038281859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9668816347567092025521239 14503224521350638038281859)
              ·
                refine ⟨21754836782025957057422789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14503224521350638038281859 21754836782025957057422789)
                ·
                  refine ⟨4079031896629866948266773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21754836782025957057422789 4079031896629866948266773)
                  ·
                    refine ⟨191204620154525013200005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4079031896629866948266773 191204620154525013200005)
                    ·
                      rfl

theorem cell23_1117109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1117109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117109 prefixEnd_1117109 := by exact prefixLift 1117109
  have htrace : WordTrace (prefixWord ++ tailWord_1117109) baseStart_1117109 baseEnd_1117109 := by
    simpa [prefixWord, tailWord_1117109, baseEnd_1117109] using wordTrace_append hprefix tailTrace_1117109
  have hstable : (prefixWord ++ tailWord_1117109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117109).length < 2 ^ (prefixWord ++ tailWord_1117109).sum := by decide
  have hdescent : baseEnd_1117109 < baseStart_1117109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117119 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 3]
def baseStart_1117119 : Nat := 118140960795 + 1117119 * 2 ^ 59
def prefixEnd_1117119 : Nat := 4983230072969 + 3 ^ 40 * 1117119 * 2
def baseEnd_1117119 : Nat := 573618995270120000474969

theorem tailTrace_1117119 : CollatzResearch.WordTrace tailWord_1117119 prefixEnd_1117119 573618995270120000474969 := by
  unfold tailWord_1117119
  simp only [CollatzResearch.WordTrace]
  refine ⟨40744677239876126580842411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27163118159917417720561607 40744677239876126580842411)
  ·
    refine ⟨61117015859814189871263617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40744677239876126580842411 61117015859814189871263617)
    ·
      refine ⟨45837761894860642403447713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61117015859814189871263617 45837761894860642403447713)
      ·
        refine ⟨34378321421145481802585785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45837761894860642403447713 34378321421145481802585785)
        ·
          refine ⟨25783741065859111351939339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34378321421145481802585785 25783741065859111351939339)
          ·
            refine ⟨38675611598788667027909009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25783741065859111351939339 38675611598788667027909009)
            ·
              refine ⟨29006708699091500270931757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38675611598788667027909009 29006708699091500270931757)
              ·
                refine ⟨10877515762159312601599409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29006708699091500270931757 10877515762159312601599409)
                ·
                  refine ⟨8158136821619484451199557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10877515762159312601599409 8158136821619484451199557)
                  ·
                    refine ⟨1529650654053653334599917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8158136821619484451199557 1529650654053653334599917)
                    ·
                      refine ⟨573618995270120000474969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1529650654053653334599917 573618995270120000474969)
                      ·
                        rfl

theorem cell23_1117119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_1117119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117119 prefixEnd_1117119 := by exact prefixLift 1117119
  have htrace : WordTrace (prefixWord ++ tailWord_1117119) baseStart_1117119 baseEnd_1117119 := by
    simpa [prefixWord, tailWord_1117119, baseEnd_1117119] using wordTrace_append hprefix tailTrace_1117119
  have hstable : (prefixWord ++ tailWord_1117119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117119).length < 2 ^ (prefixWord ++ tailWord_1117119).sum := by decide
  have hdescent : baseEnd_1117119 < baseStart_1117119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117156 : List Nat := [2, 3, 1, 1, 1, 1, 2, 7, 5]
def baseStart_1117156 : Nat := 118140960795 + 1117156 * 2 ^ 59
def prefixEnd_1117156 : Nat := 4983230072969 + 3 ^ 40 * 1117156 * 2
def baseEnd_1117156 : Nat := 63737554894926261745811

theorem tailTrace_1117156 : CollatzResearch.WordTrace tailWord_1117156 prefixEnd_1117156 63737554894926261745811 := by
  unfold tailWord_1117156
  simp only [CollatzResearch.WordTrace]
  refine ⟨20373013370371040949969661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27164017827161387933292881 20373013370371040949969661)
  ·
    refine ⟨7639880013889140356238623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20373013370371040949969661 7639880013889140356238623)
    ·
      refine ⟨11459820020833710534357935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7639880013889140356238623 11459820020833710534357935)
      ·
        refine ⟨17189730031250565801536903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11459820020833710534357935 17189730031250565801536903)
        ·
          refine ⟨25784595046875848702305355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17189730031250565801536903 25784595046875848702305355)
          ·
            refine ⟨38676892570313773053458033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25784595046875848702305355 38676892570313773053458033)
            ·
              refine ⟨29007669427735329790093525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38676892570313773053458033 29007669427735329790093525)
              ·
                refine ⟨679867252212546791955317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29007669427735329790093525 679867252212546791955317)
                ·
                  refine ⟨63737554894926261745811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 679867252212546791955317 63737554894926261745811)
                  ·
                    rfl

theorem cell23_1117156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_1117156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117156 prefixEnd_1117156 := by exact prefixLift 1117156
  have htrace : WordTrace (prefixWord ++ tailWord_1117156) baseStart_1117156 baseEnd_1117156 := by
    simpa [prefixWord, tailWord_1117156, baseEnd_1117156] using wordTrace_append hprefix tailTrace_1117156
  have hstable : (prefixWord ++ tailWord_1117156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117156).length < 2 ^ (prefixWord ++ tailWord_1117156).sum := by decide
  have hdescent : baseEnd_1117156 < baseStart_1117156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117176 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 2, 5, 2]
def baseStart_1117176 : Nat := 118140960795 + 1117176 * 2 ^ 59
def prefixEnd_1117176 : Nat := 4983230072969 + 3 ^ 40 * 1117176 * 2
def baseEnd_1117176 : Nat := 573648263667426277462207

theorem tailTrace_1117176 : CollatzResearch.WordTrace tailWord_1117176 prefixEnd_1117176 573648263667426277462207 := by
  unfold tailWord_1117176
  simp only [CollatzResearch.WordTrace]
  refine ⟨20373378100334812657833691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27164504133779750210444921 20373378100334812657833691)
  ·
    refine ⟨30560067150502218986750537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20373378100334812657833691 30560067150502218986750537)
    ·
      refine ⟨22920050362876664240062903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30560067150502218986750537 22920050362876664240062903)
      ·
        refine ⟨34380075544314996360094355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22920050362876664240062903 34380075544314996360094355)
        ·
          refine ⟨51570113316472494540141533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34380075544314996360094355 51570113316472494540141533)
          ·
            refine ⟨19338792493677185452553075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51570113316472494540141533 19338792493677185452553075)
            ·
              refine ⟨29008188740515778178829613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19338792493677185452553075 29008188740515778178829613)
              ·
                refine ⟨10878070777693416817061105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29008188740515778178829613 10878070777693416817061105)
                ·
                  refine ⟨8158553083270062612795829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10878070777693416817061105 8158553083270062612795829)
                  ·
                    refine ⟨764864351556568369949609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8158553083270062612795829 764864351556568369949609)
                    ·
                      refine ⟨573648263667426277462207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764864351556568369949609 573648263667426277462207)
                      ·
                        rfl

theorem cell23_1117176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_1117176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117176 prefixEnd_1117176 := by exact prefixLift 1117176
  have htrace : WordTrace (prefixWord ++ tailWord_1117176) baseStart_1117176 baseEnd_1117176 := by
    simpa [prefixWord, tailWord_1117176, baseEnd_1117176] using wordTrace_append hprefix tailTrace_1117176
  have hstable : (prefixWord ++ tailWord_1117176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117176).length < 2 ^ (prefixWord ++ tailWord_1117176).sum := by decide
  have hdescent : baseEnd_1117176 < baseStart_1117176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117283 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 4, 3, 2]
def baseStart_1117283 : Nat := 118140960795 + 1117283 * 2 ^ 59
def prefixEnd_1117283 : Nat := 4983230072969 + 3 ^ 40 * 1117283 * 2
def baseEnd_1117283 : Nat := 573703206097457358824215

theorem tailTrace_1117283 : CollatzResearch.WordTrace tailWord_1117283 prefixEnd_1117283 573703206097457358824215 := by
  unfold tailWord_1117283
  simp only [CollatzResearch.WordTrace]
  refine ⟨40750658811281982589812503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27167105874187988393208335 40750658811281982589812503)
  ·
    refine ⟨61125988216922973884718755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40750658811281982589812503 61125988216922973884718755)
    ·
      refine ⟨91688982325384460827078133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61125988216922973884718755 91688982325384460827078133)
      ·
        refine ⟨8595842093004793202538575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91688982325384460827078133 8595842093004793202538575)
        ·
          refine ⟨12893763139507189803807863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8595842093004793202538575 12893763139507189803807863)
          ·
            refine ⟨19340644709260784705711795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12893763139507189803807863 19340644709260784705711795)
            ·
              refine ⟨29010967063891177058567693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19340644709260784705711795 29010967063891177058567693)
              ·
                refine ⟨10879112648959191396962885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29010967063891177058567693 10879112648959191396962885)
                ·
                  refine ⟨2039833621679848386930541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10879112648959191396962885 2039833621679848386930541)
                  ·
                    refine ⟨764937608129943145098953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2039833621679848386930541 764937608129943145098953)
                    ·
                      refine ⟨573703206097457358824215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764937608129943145098953 573703206097457358824215)
                      ·
                        rfl

theorem cell23_1117283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_1117283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117283 prefixEnd_1117283 := by exact prefixLift 1117283
  have htrace : WordTrace (prefixWord ++ tailWord_1117283) baseStart_1117283 baseEnd_1117283 := by
    simpa [prefixWord, tailWord_1117283, baseEnd_1117283] using wordTrace_append hprefix tailTrace_1117283
  have hstable : (prefixWord ++ tailWord_1117283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117283).length < 2 ^ (prefixWord ++ tailWord_1117283).sum := by decide
  have hdescent : baseEnd_1117283 < baseStart_1117283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117290 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1117290 : Nat := 118140960795 + 1117290 * 2 ^ 59
def prefixEnd_1117290 : Nat := 4983230072969 + 3 ^ 40 * 1117290 * 2
def baseEnd_1117290 : Nat := 573706800462038831436683

theorem tailTrace_1117290 : CollatzResearch.WordTrace tailWord_1117290 prefixEnd_1117290 573706800462038831436683 := by
  unfold tailWord_1117290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187728530564155696329331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27167276081504415190211549 10187728530564155696329331)
  ·
    refine ⟨15281592795846233544493997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10187728530564155696329331 15281592795846233544493997)
    ·
      refine ⟨5730597298442337579185249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15281592795846233544493997 5730597298442337579185249)
      ·
        refine ⟨4297947973831753184388937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5730597298442337579185249 4297947973831753184388937)
        ·
          refine ⟨3223460980373814888291703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4297947973831753184388937 3223460980373814888291703)
          ·
            refine ⟨4835191470560722332437555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223460980373814888291703 4835191470560722332437555)
            ·
              refine ⟨7252787205841083498656333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4835191470560722332437555 7252787205841083498656333)
              ·
                refine ⟨2719795202190406311996125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7252787205841083498656333 2719795202190406311996125)
                ·
                  refine ⟨1019923200821402366998547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2719795202190406311996125 1019923200821402366998547)
                  ·
                    refine ⟨1529884801232103550497821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1019923200821402366998547 1529884801232103550497821)
                    ·
                      refine ⟨573706800462038831436683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1529884801232103550497821 573706800462038831436683)
                      ·
                        rfl

theorem cell23_1117290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1117290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117290 prefixEnd_1117290 := by exact prefixLift 1117290
  have htrace : WordTrace (prefixWord ++ tailWord_1117290) baseStart_1117290 baseEnd_1117290 := by
    simpa [prefixWord, tailWord_1117290, baseEnd_1117290] using wordTrace_append hprefix tailTrace_1117290
  have hstable : (prefixWord ++ tailWord_1117290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117290).length < 2 ^ (prefixWord ++ tailWord_1117290).sum := by decide
  have hdescent : baseEnd_1117290 < baseStart_1117290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117330 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1117330 : Nat := 118140960795 + 1117330 * 2 ^ 59
def prefixEnd_1117330 : Nat := 4983230072969 + 3 ^ 40 * 1117330 * 2
def baseEnd_1117330 : Nat := 573727339688218674936499

theorem tailTrace_1117330 : CollatzResearch.WordTrace tailWord_1117330 prefixEnd_1117330 573727339688218674936499 := by
  unfold tailWord_1117330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188093260527927404193361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27168248694741139744515629 10188093260527927404193361)
  ·
    refine ⟨7641069945395945553145021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10188093260527927404193361 7641069945395945553145021)
    ·
      refine ⟨2865401229523479582429383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7641069945395945553145021 2865401229523479582429383)
      ·
        refine ⟨4298101844285219373644075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2865401229523479582429383 4298101844285219373644075)
        ·
          refine ⟨6447152766427829060466113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4298101844285219373644075 6447152766427829060466113)
          ·
            refine ⟨4835364574820871795349585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6447152766427829060466113 4835364574820871795349585)
            ·
              refine ⟨3626523431115653846512189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4835364574820871795349585 3626523431115653846512189)
              ·
                refine ⟨1359946286668370192442071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3626523431115653846512189 1359946286668370192442071)
                ·
                  refine ⟨2039919430002555288663107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359946286668370192442071 2039919430002555288663107)
                  ·
                    refine ⟨3059879145003832932994661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2039919430002555288663107 3059879145003832932994661)
                    ·
                      refine ⟨573727339688218674936499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3059879145003832932994661 573727339688218674936499)
                      ·
                        rfl

theorem cell23_1117330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1117330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117330 prefixEnd_1117330 := by exact prefixLift 1117330
  have htrace : WordTrace (prefixWord ++ tailWord_1117330) baseStart_1117330 baseEnd_1117330 := by
    simpa [prefixWord, tailWord_1117330, baseEnd_1117330] using wordTrace_append hprefix tailTrace_1117330
  have hstable : (prefixWord ++ tailWord_1117330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117330).length < 2 ^ (prefixWord ++ tailWord_1117330).sum := by decide
  have hdescent : baseEnd_1117330 < baseStart_1117330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117336 : List Nat := [2, 1, 2, 4, 2, 1, 11]
def baseStart_1117336 : Nat := 118140960795 + 1117336 * 2 ^ 59
def prefixEnd_1117336 : Nat := 4983230072969 + 3 ^ 40 * 1117336 * 2
def baseEnd_1117336 : Nat := 7083091612001798166191

theorem tailTrace_1117336 : CollatzResearch.WordTrace tailWord_1117336 prefixEnd_1117336 7083091612001798166191 := by
  unfold tailWord_1117336
  simp only [CollatzResearch.WordTrace]
  refine ⟨20376295940044986320745931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27168394586726648427661241 20376295940044986320745931)
  ·
    refine ⟨30564443910067479481118897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20376295940044986320745931 30564443910067479481118897)
    ·
      refine ⟨22923332932550609610839173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30564443910067479481118897 22923332932550609610839173)
      ·
        refine ⟨4298124924853239302032345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22923332932550609610839173 4298124924853239302032345)
        ·
          refine ⟨3223593693639929476524259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4298124924853239302032345 3223593693639929476524259)
          ·
            refine ⟨4835390540459894214786389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223593693639929476524259 4835390540459894214786389)
            ·
              refine ⟨7083091612001798166191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4835390540459894214786389 7083091612001798166191)
              ·
                rfl

theorem cell23_1117336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 11].length) (baseStart_1117336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117336 prefixEnd_1117336 := by exact prefixLift 1117336
  have htrace : WordTrace (prefixWord ++ tailWord_1117336) baseStart_1117336 baseEnd_1117336 := by
    simpa [prefixWord, tailWord_1117336, baseEnd_1117336] using wordTrace_append hprefix tailTrace_1117336
  have hstable : (prefixWord ++ tailWord_1117336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117336).length < 2 ^ (prefixWord ++ tailWord_1117336).sum := by decide
  have hdescent : baseEnd_1117336 < baseStart_1117336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117347 : List Nat := [1, 1, 1, 4, 1, 1, 1, 8, 1, 2, 2]
def baseStart_1117347 : Nat := 118140960795 + 1117347 * 2 ^ 59
def prefixEnd_1117347 : Nat := 4983230072969 + 3 ^ 40 * 1117347 * 2
def baseEnd_1117347 : Nat := 573736068859345108423921

theorem tailTrace_1117347 : CollatzResearch.WordTrace tailWord_1117347 prefixEnd_1117347 573736068859345108423921 := by
  unfold tailWord_1117347
  simp only [CollatzResearch.WordTrace]
  refine ⟨40752993083050121520142295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27168662055366747680094863 40752993083050121520142295)
  ·
    refine ⟨61129489624575182280213443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40752993083050121520142295 61129489624575182280213443)
    ·
      refine ⟨91694234436862773420320165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61129489624575182280213443 91694234436862773420320165)
      ·
        refine ⟨17192668956911770016310031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91694234436862773420320165 17192668956911770016310031)
        ·
          refine ⟨25789003435367655024465047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17192668956911770016310031 25789003435367655024465047)
          ·
            refine ⟨38683505153051482536697571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25789003435367655024465047 38683505153051482536697571)
            ·
              refine ⟨58025257729577223805046357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38683505153051482536697571 58025257729577223805046357)
              ·
                refine ⟨679983489018483091465387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 58025257729577223805046357 679983489018483091465387)
                ·
                  refine ⟨1019975233527724637198081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679983489018483091465387 1019975233527724637198081)
                  ·
                    refine ⟨764981425145793477898561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1019975233527724637198081 764981425145793477898561)
                    ·
                      refine ⟨573736068859345108423921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 764981425145793477898561 573736068859345108423921)
                      ·
                        rfl

theorem cell23_1117347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_1117347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117347 prefixEnd_1117347 := by exact prefixLift 1117347
  have htrace : WordTrace (prefixWord ++ tailWord_1117347) baseStart_1117347 baseEnd_1117347 := by
    simpa [prefixWord, tailWord_1117347, baseEnd_1117347] using wordTrace_append hprefix tailTrace_1117347
  have hstable : (prefixWord ++ tailWord_1117347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117347).length < 2 ^ (prefixWord ++ tailWord_1117347).sum := by decide
  have hdescent : baseEnd_1117347 < baseStart_1117347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117357 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1117357 : Nat := 118140960795 + 1117357 * 2 ^ 59
def prefixEnd_1117357 : Nat := 4983230072969 + 3 ^ 40 * 1117357 * 2
def baseEnd_1117357 : Nat := 191247067888630023099625

theorem tailTrace_1117357 : CollatzResearch.WordTrace tailWord_1117357 prefixEnd_1117357 191247067888630023099625 := by
  unfold tailWord_1117357
  simp only [CollatzResearch.WordTrace]
  refine ⟨40753357813013893228006325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27168905208675928818670883 40753357813013893228006325)
  ·
    refine ⟨3820627294970052490125593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40753357813013893228006325 3820627294970052490125593)
    ·
      refine ⟨2865470471227539367594195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3820627294970052490125593 2865470471227539367594195)
      ·
        refine ⟨4298205706841309051391293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2865470471227539367594195 4298205706841309051391293)
        ·
          refine ⟨1611827140065490894271735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4298205706841309051391293 1611827140065490894271735)
          ·
            refine ⟨2417740710098236341407603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611827140065490894271735 2417740710098236341407603)
            ·
              refine ⟨3626611065147354512111405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417740710098236341407603 3626611065147354512111405)
              ·
                refine ⟨1359979149430257942041777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3626611065147354512111405 1359979149430257942041777)
                ·
                  refine ⟨1019984362072693456531333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1359979149430257942041777 1019984362072693456531333)
                  ·
                    refine ⟨191247067888630023099625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1019984362072693456531333 191247067888630023099625)
                    ·
                      rfl

theorem cell23_1117357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1117357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117357 prefixEnd_1117357 := by exact prefixLift 1117357
  have htrace : WordTrace (prefixWord ++ tailWord_1117357) baseStart_1117357 baseEnd_1117357 := by
    simpa [prefixWord, tailWord_1117357, baseEnd_1117357] using wordTrace_append hprefix tailTrace_1117357
  have hstable : (prefixWord ++ tailWord_1117357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117357).length < 2 ^ (prefixWord ++ tailWord_1117357).sum := by decide
  have hdescent : baseEnd_1117357 < baseStart_1117357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117397 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1117397 : Nat := 118140960795 + 1117397 * 2 ^ 59
def prefixEnd_1117397 : Nat := 4983230072969 + 3 ^ 40 * 1117397 * 2
def baseEnd_1117397 : Nat := 573761742892069912798691

theorem tailTrace_1117397 : CollatzResearch.WordTrace tailWord_1117397 prefixEnd_1117397 573761742892069912798691 := by
  unfold tailWord_1117397
  simp only [CollatzResearch.WordTrace]
  refine ⟨40754816732868980059462445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27169877821912653372974963 40754816732868980059462445)
  ·
    refine ⟨15283056274825867522298417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40754816732868980059462445 15283056274825867522298417)
    ·
      refine ⟨11462292206119400641723813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15283056274825867522298417 11462292206119400641723813)
      ·
        refine ⟨2149179788647387620323215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11462292206119400641723813 2149179788647387620323215)
        ·
          refine ⟨3223769682971081430484823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149179788647387620323215 3223769682971081430484823)
          ·
            refine ⟨4835654524456622145727235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223769682971081430484823 4835654524456622145727235)
            ·
              refine ⟨7253481786684933218590853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4835654524456622145727235 7253481786684933218590853)
              ·
                refine ⟨1360027835003424978485785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7253481786684933218590853 1360027835003424978485785)
                ·
                  refine ⟨1020020876252568733864339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360027835003424978485785 1020020876252568733864339)
                  ·
                    refine ⟨1530031314378853100796509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1020020876252568733864339 1530031314378853100796509)
                    ·
                      refine ⟨573761742892069912798691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1530031314378853100796509 573761742892069912798691)
                      ·
                        rfl

theorem cell23_1117397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1117397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117397 prefixEnd_1117397 := by exact prefixLift 1117397
  have htrace : WordTrace (prefixWord ++ tailWord_1117397) baseStart_1117397 baseEnd_1117397 := by
    simpa [prefixWord, tailWord_1117397, baseEnd_1117397] using wordTrace_append hprefix tailTrace_1117397
  have hstable : (prefixWord ++ tailWord_1117397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117397).length < 2 ^ (prefixWord ++ tailWord_1117397).sum := by decide
  have hdescent : baseEnd_1117397 < baseStart_1117397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117398 : List Nat := [5, 2, 1, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_1117398 : Nat := 118140960795 + 1117398 * 2 ^ 59
def prefixEnd_1117398 : Nat := 4983230072969 + 3 ^ 40 * 1117398 * 2
def baseEnd_1117398 : Nat := 573762256372724408886187

theorem tailTrace_1117398 : CollatzResearch.WordTrace tailWord_1117398 prefixEnd_1117398 573762256372724408886187 := by
  unfold tailWord_1117398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547178325366584826890553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27169902137243571486832565 2547178325366584826890553)
  ·
    refine ⟨1910383744024938620167915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2547178325366584826890553 1910383744024938620167915)
    ·
      refine ⟨2865575616037407930251873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1910383744024938620167915 2865575616037407930251873)
      ·
        refine ⟨2149181712028055947688905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2865575616037407930251873 2149181712028055947688905)
        ·
          refine ⟨1611886284021041960766679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2149181712028055947688905 1611886284021041960766679)
          ·
            refine ⟨2417829426031562941150019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611886284021041960766679 2417829426031562941150019)
            ·
              refine ⟨3626744139047344411725029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417829426031562941150019 3626744139047344411725029)
              ·
                refine ⟨680014526071377077198443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3626744139047344411725029 680014526071377077198443)
                ·
                  refine ⟨1020021789107065615797665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680014526071377077198443 1020021789107065615797665)
                  ·
                    refine ⟨765016341830299211848249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1020021789107065615797665 765016341830299211848249)
                    ·
                      refine ⟨573762256372724408886187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765016341830299211848249 573762256372724408886187)
                      ·
                        rfl

theorem cell23_1117398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_1117398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117398 prefixEnd_1117398 := by exact prefixLift 1117398
  have htrace : WordTrace (prefixWord ++ tailWord_1117398) baseStart_1117398 baseEnd_1117398 := by
    simpa [prefixWord, tailWord_1117398, baseEnd_1117398] using wordTrace_append hprefix tailTrace_1117398
  have hstable : (prefixWord ++ tailWord_1117398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117398).length < 2 ^ (prefixWord ++ tailWord_1117398).sum := by decide
  have hdescent : baseEnd_1117398 < baseStart_1117398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117420 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 1, 4, 2]
def baseStart_1117420 : Nat := 118140960795 + 1117420 * 2 ^ 59
def prefixEnd_1117420 : Nat := 4983230072969 + 3 ^ 40 * 1117420 * 2
def baseEnd_1117420 : Nat := 573773552947123322811085

theorem tailTrace_1117420 : CollatzResearch.WordTrace tailWord_1117420 prefixEnd_1117420 573773552947123322811085 := by
  unfold tailWord_1117420
  simp only [CollatzResearch.WordTrace]
  refine ⟨20377827805892827493774857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27170437074523769991699809 20377827805892827493774857)
  ·
    refine ⟨15283370854419620620331143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20377827805892827493774857 15283370854419620620331143)
    ·
      refine ⟨22925056281629430930496715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15283370854419620620331143 22925056281629430930496715)
      ·
        refine ⟨34387584422444146395745073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22925056281629430930496715 34387584422444146395745073)
        ·
          refine ⟨25790688316833109796808805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34387584422444146395745073 25790688316833109796808805)
          ·
            refine ⟨4835754059406208086901651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25790688316833109796808805 4835754059406208086901651)
            ·
              refine ⟨7253631089109312130352477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4835754059406208086901651 7253631089109312130352477)
              ·
                refine ⟨2720111658415992048882179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7253631089109312130352477 2720111658415992048882179)
                ·
                  refine ⟨4080167487623988073323269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720111658415992048882179 4080167487623988073323269)
                  ·
                    refine ⟨765031403929497763748113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4080167487623988073323269 765031403929497763748113)
                    ·
                      refine ⟨573773552947123322811085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765031403929497763748113 573773552947123322811085)
                      ·
                        rfl

theorem cell23_1117420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_1117420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117420 prefixEnd_1117420 := by exact prefixLift 1117420
  have htrace : WordTrace (prefixWord ++ tailWord_1117420) baseStart_1117420 baseEnd_1117420 := by
    simpa [prefixWord, tailWord_1117420, baseEnd_1117420] using wordTrace_append hprefix tailTrace_1117420
  have hstable : (prefixWord ++ tailWord_1117420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117420).length < 2 ^ (prefixWord ++ tailWord_1117420).sum := by decide
  have hdescent : baseEnd_1117420 < baseStart_1117420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117454 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_1117454 : Nat := 118140960795 + 1117454 * 2 ^ 59
def prefixEnd_1117454 : Nat := 4983230072969 + 3 ^ 40 * 1117454 * 2
def baseEnd_1117454 : Nat := 573791011289376189785929

theorem tailTrace_1117454 : CollatzResearch.WordTrace tailWord_1117454 prefixEnd_1117454 573791011289376189785929 := by
  unfold tailWord_1117454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5094611961707809849285927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27171263795774985862858277 5094611961707809849285927)
  ·
    refine ⟨7641917942561714773928891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5094611961707809849285927 7641917942561714773928891)
    ·
      refine ⟨11462876913842572160893337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7641917942561714773928891 11462876913842572160893337)
      ·
        refine ⟨8597157685381929120670003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11462876913842572160893337 8597157685381929120670003)
        ·
          refine ⟨12895736528072893681005005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8597157685381929120670003 12895736528072893681005005)
          ·
            refine ⟨4835901198027335130376877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12895736528072893681005005 4835901198027335130376877)
            ·
              refine ⟨1813462949260250673891329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4835901198027335130376877 1813462949260250673891329)
              ·
                refine ⟨1360097211945188005418497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1813462949260250673891329 1360097211945188005418497)
                ·
                  refine ⟨1020072908958891004063873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360097211945188005418497 1020072908958891004063873)
                  ·
                    refine ⟨765054681719168253047905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1020072908958891004063873 765054681719168253047905)
                    ·
                      refine ⟨573791011289376189785929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765054681719168253047905 573791011289376189785929)
                      ·
                        rfl

theorem cell23_1117454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_1117454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117454 prefixEnd_1117454 := by exact prefixLift 1117454
  have htrace : WordTrace (prefixWord ++ tailWord_1117454) baseStart_1117454 baseEnd_1117454 := by
    simpa [prefixWord, tailWord_1117454, baseEnd_1117454] using wordTrace_append hprefix tailTrace_1117454
  have hstable : (prefixWord ++ tailWord_1117454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117454).length < 2 ^ (prefixWord ++ tailWord_1117454).sum := by decide
  have hdescent : baseEnd_1117454 < baseStart_1117454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117471 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 2, 2, 2]
def baseStart_1117471 : Nat := 118140960795 + 1117471 * 2 ^ 59
def prefixEnd_1117471 : Nat := 4983230072969 + 3 ^ 40 * 1117471 * 2
def baseEnd_1117471 : Nat := 573799740460502623273351

theorem tailTrace_1117471 : CollatzResearch.WordTrace tailWord_1117471 prefixEnd_1117471 573799740460502623273351 := by
  unfold tailWord_1117471
  simp only [CollatzResearch.WordTrace]
  refine ⟨40757515734600890697656267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27171677156400593798437511 40757515734600890697656267)
  ·
    refine ⟨61136273601901336046484401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40757515734600890697656267 61136273601901336046484401)
    ·
      refine ⟨45852205201426002034863301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61136273601901336046484401 45852205201426002034863301)
      ·
        refine ⟨8597288475267375381536869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45852205201426002034863301 8597288475267375381536869)
        ·
          refine ⟨1611991589112632884038163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8597288475267375381536869 1611991589112632884038163)
          ·
            refine ⟨2417987383668949326057245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611991589112632884038163 2417987383668949326057245)
            ·
              refine ⟨906745268875855997271467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2417987383668949326057245 906745268875855997271467)
              ·
                refine ⟨1360117903313783995907201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906745268875855997271467 1360117903313783995907201)
                ·
                  refine ⟨1020088427485337996930401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360117903313783995907201 1020088427485337996930401)
                  ·
                    refine ⟨765066320614003497697801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1020088427485337996930401 765066320614003497697801)
                    ·
                      refine ⟨573799740460502623273351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765066320614003497697801 573799740460502623273351)
                      ·
                        rfl

theorem cell23_1117471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_1117471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117471 prefixEnd_1117471 := by exact prefixLift 1117471
  have htrace : WordTrace (prefixWord ++ tailWord_1117471) baseStart_1117471 baseEnd_1117471 := by
    simpa [prefixWord, tailWord_1117471, baseEnd_1117471] using wordTrace_append hprefix tailTrace_1117471
  have hstable : (prefixWord ++ tailWord_1117471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117471).length < 2 ^ (prefixWord ++ tailWord_1117471).sum := by decide
  have hdescent : baseEnd_1117471 < baseStart_1117471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117571 : List Nat := [1, 1, 1, 3, 5, 3, 2, 2, 1, 4]
def baseStart_1117571 : Nat := 118140960795 + 1117571 * 2 ^ 59
def prefixEnd_1117571 : Nat := 4983230072969 + 3 ^ 40 * 1117571 * 2
def baseEnd_1117571 : Nat := 191283696175317410674297

theorem tailTrace_1117571 : CollatzResearch.WordTrace tailWord_1117571 prefixEnd_1117571 191283696175317410674297 := by
  unfold tailWord_1117571
  simp only [CollatzResearch.WordTrace]
  refine ⟨40761163034238607776296567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27174108689492405184197711 40761163034238607776296567)
  ·
    refine ⟨61141744551357911664444851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40761163034238607776296567 61141744551357911664444851)
    ·
      refine ⟨91712616827036867496667277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61141744551357911664444851 91712616827036867496667277)
      ·
        refine ⟨34392231310138825311250229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91712616827036867496667277 34392231310138825311250229)
        ·
          refine ⟨3224271685325514872929709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34392231310138825311250229 3224271685325514872929709)
          ·
            refine ⟨1209101881997068077348641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3224271685325514872929709 1209101881997068077348641)
            ·
              refine ⟨906826411497801058011481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209101881997068077348641 906826411497801058011481)
              ·
                refine ⟨680119808623350793508611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906826411497801058011481 680119808623350793508611)
                ·
                  refine ⟨1020179712935026190262917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680119808623350793508611 1020179712935026190262917)
                  ·
                    refine ⟨191283696175317410674297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1020179712935026190262917 191283696175317410674297)
                    ·
                      rfl

theorem cell23_1117571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 4].length) (baseStart_1117571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117571 prefixEnd_1117571 := by exact prefixLift 1117571
  have htrace : WordTrace (prefixWord ++ tailWord_1117571) baseStart_1117571 baseEnd_1117571 := by
    simpa [prefixWord, tailWord_1117571, baseEnd_1117571] using wordTrace_append hprefix tailTrace_1117571
  have hstable : (prefixWord ++ tailWord_1117571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117571).length < 2 ^ (prefixWord ++ tailWord_1117571).sum := by decide
  have hdescent : baseEnd_1117571 < baseStart_1117571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117598 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_1117598 : Nat := 118140960795 + 1117598 * 2 ^ 59
def prefixEnd_1117598 : Nat := 4983230072969 + 3 ^ 40 * 1117598 * 2
def baseEnd_1117598 : Nat := 573864952503623626385267

theorem tailTrace_1117598 : CollatzResearch.WordTrace tailWord_1117598 prefixEnd_1117598 573864952503623626385267 := by
  unfold tailWord_1117598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095268475642598923441181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27174765203427194258352965 5095268475642598923441181)
  ·
    refine ⟨1910725678365974596290443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5095268475642598923441181 1910725678365974596290443)
    ·
      refine ⟨2866088517548961894435665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1910725678365974596290443 2866088517548961894435665)
      ·
        refine ⟨2149566388161721420826749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2866088517548961894435665 2149566388161721420826749)
        ·
          refine ⟨806087395560645532810031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2149566388161721420826749 806087395560645532810031)
          ·
            refine ⟨1209131093340968299215047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806087395560645532810031 1209131093340968299215047)
            ·
              refine ⟨1813696640011452448822571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209131093340968299215047 1813696640011452448822571)
              ·
                refine ⟨2720544960017178673233857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813696640011452448822571 2720544960017178673233857)
                ·
                  refine ⟨2040408720012884004925393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720544960017178673233857 2040408720012884004925393)
                  ·
                    refine ⟨1530306540009663003694045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2040408720012884004925393 1530306540009663003694045)
                    ·
                      refine ⟨573864952503623626385267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1530306540009663003694045 573864952503623626385267)
                      ·
                        rfl

theorem cell23_1117598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_1117598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117598 prefixEnd_1117598 := by exact prefixLift 1117598
  have htrace : WordTrace (prefixWord ++ tailWord_1117598) baseStart_1117598 baseEnd_1117598 := by
    simpa [prefixWord, tailWord_1117598, baseEnd_1117598] using wordTrace_append hprefix tailTrace_1117598
  have hstable : (prefixWord ++ tailWord_1117598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117598).length < 2 ^ (prefixWord ++ tailWord_1117598).sum := by decide
  have hdescent : baseEnd_1117598 < baseStart_1117598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117600 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1117600 : Nat := 118140960795 + 1117600 * 2 ^ 59
def prefixEnd_1117600 : Nat := 4983230072969 + 3 ^ 40 * 1117600 * 2
def baseEnd_1117600 : Nat := 573865979464932618560257

theorem tailTrace_1117600 : CollatzResearch.WordTrace tailWord_1117600 prefixEnd_1117600 573865979464932618560257 := by
  unfold tailWord_1117600
  simp only [CollatzResearch.WordTrace]
  refine ⟨20381110375566772864551127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27174813834089030486068169 20381110375566772864551127)
  ·
    refine ⟨30571665563350159296826691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20381110375566772864551127 30571665563350159296826691)
    ·
      refine ⟨45857498345025238945240037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30571665563350159296826691 45857498345025238945240037)
      ·
        refine ⟨8598280939692232302232507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45857498345025238945240037 8598280939692232302232507)
        ·
          refine ⟨12897421409538348453348761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8598280939692232302232507 12897421409538348453348761)
          ·
            refine ⟨9673066057153761340011571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12897421409538348453348761 9673066057153761340011571)
            ·
              refine ⟨14509599085730642010017357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9673066057153761340011571 14509599085730642010017357)
              ·
                refine ⟨5441099657148990753756509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14509599085730642010017357 5441099657148990753756509)
                ·
                  refine ⟨2040412371430871532658691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5441099657148990753756509 2040412371430871532658691)
                  ·
                    refine ⟨3060618557146307298988037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040412371430871532658691 3060618557146307298988037)
                    ·
                      refine ⟨573865979464932618560257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3060618557146307298988037 573865979464932618560257)
                      ·
                        rfl

theorem cell23_1117600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1117600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117600 prefixEnd_1117600 := by exact prefixLift 1117600
  have htrace : WordTrace (prefixWord ++ tailWord_1117600) baseStart_1117600 baseEnd_1117600 := by
    simpa [prefixWord, tailWord_1117600, baseEnd_1117600] using wordTrace_append hprefix tailTrace_1117600
  have hstable : (prefixWord ++ tailWord_1117600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117600).length < 2 ^ (prefixWord ++ tailWord_1117600).sum := by decide
  have hdescent : baseEnd_1117600 < baseStart_1117600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117617 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1117617 : Nat := 118140960795 + 1117617 * 2 ^ 59
def prefixEnd_1117617 : Nat := 4983230072969 + 3 ^ 40 * 1117617 * 2
def baseEnd_1117617 : Nat := 573874708636059052047679

theorem tailTrace_1117617 : CollatzResearch.WordTrace tailWord_1117617 prefixEnd_1117617 573874708636059052047679 := by
  unfold tailWord_1117617
  simp only [CollatzResearch.WordTrace]
  refine ⟨40762840792071957632471105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27175227194714638421647403 40762840792071957632471105)
  ·
    refine ⟨30572130594053968224353329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40762840792071957632471105 30572130594053968224353329)
    ·
      refine ⟨22929097945540476168264997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30572130594053968224353329 22929097945540476168264997)
      ·
        refine ⟨4299205864788839281549687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22929097945540476168264997 4299205864788839281549687)
        ·
          refine ⟨6448808797183258922324531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299205864788839281549687 6448808797183258922324531)
          ·
            refine ⟨9673213195774888383486797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6448808797183258922324531 9673213195774888383486797)
            ·
              refine ⟨3627454948415583143807549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9673213195774888383486797 3627454948415583143807549)
              ·
                refine ⟨1360295605655843678927831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3627454948415583143807549 1360295605655843678927831)
                ·
                  refine ⟨2040443408483765518391747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360295605655843678927831 2040443408483765518391747)
                  ·
                    refine ⟨3060665112725648277587621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040443408483765518391747 3060665112725648277587621)
                    ·
                      refine ⟨573874708636059052047679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3060665112725648277587621 573874708636059052047679)
                      ·
                        rfl

theorem cell23_1117617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1117617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117617 prefixEnd_1117617 := by exact prefixLift 1117617
  have htrace : WordTrace (prefixWord ++ tailWord_1117617) baseStart_1117617 baseEnd_1117617 := by
    simpa [prefixWord, tailWord_1117617, baseEnd_1117617] using wordTrace_append hprefix tailTrace_1117617
  have hstable : (prefixWord ++ tailWord_1117617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117617).length < 2 ^ (prefixWord ++ tailWord_1117617).sum := by decide
  have hdescent : baseEnd_1117617 < baseStart_1117617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117623 : List Nat := [1, 1, 3, 1, 3, 2, 12]
def baseStart_1117623 : Nat := 118140960795 + 1117623 * 2 ^ 59
def prefixEnd_1117623 : Nat := 4983230072969 + 3 ^ 40 * 1117623 * 2
def baseEnd_1117623 : Nat := 7084910981728222574971

theorem tailTrace_1117623 : CollatzResearch.WordTrace tailWord_1117623 prefixEnd_1117623 7084910981728222574971 := by
  unfold tailWord_1117623
  simp only [CollatzResearch.WordTrace]
  refine ⟨40763059630050220657189523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27175373086700147104793015 40763059630050220657189523)
  ·
    refine ⟨61144589445075330985784285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40763059630050220657189523 61144589445075330985784285)
    ·
      refine ⟨22929221041903249119669107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61144589445075330985784285 22929221041903249119669107)
      ·
        refine ⟨34393831562854873679503661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22929221041903249119669107 34393831562854873679503661)
        ·
          refine ⟨12897686836070577629813873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34393831562854873679503661 12897686836070577629813873)
          ·
            refine ⟨9673265127052933222360405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12897686836070577629813873 9673265127052933222360405)
            ·
              refine ⟨7084910981728222574971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 9673265127052933222360405 7084910981728222574971)
              ·
                rfl

theorem cell23_1117623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 12].length) (baseStart_1117623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117623 prefixEnd_1117623 := by exact prefixLift 1117623
  have htrace : WordTrace (prefixWord ++ tailWord_1117623) baseStart_1117623 baseEnd_1117623 := by
    simpa [prefixWord, tailWord_1117623, baseEnd_1117623] using wordTrace_append hprefix tailTrace_1117623
  have hstable : (prefixWord ++ tailWord_1117623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117623).length < 2 ^ (prefixWord ++ tailWord_1117623).sum := by decide
  have hdescent : baseEnd_1117623 < baseStart_1117623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117630 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1117630 : Nat := 118140960795 + 1117630 * 2 ^ 59
def prefixEnd_1117630 : Nat := 4983230072969 + 3 ^ 40 * 1117630 * 2
def baseEnd_1117630 : Nat := 573881383884567501185119

theorem tailTrace_1117630 : CollatzResearch.WordTrace tailWord_1117630 prefixEnd_1117630 573881383884567501185119 := by
  unfold tailWord_1117630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095414367628107606586793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27175543294016573901796229 5095414367628107606586793)
  ·
    refine ⟨3821560775721080704940095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5095414367628107606586793 3821560775721080704940095)
    ·
      refine ⟨5732341163581621057410143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3821560775721080704940095 5732341163581621057410143)
      ·
        refine ⟨8598511745372431586115215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5732341163581621057410143 8598511745372431586115215)
        ·
          refine ⟨12897767618058647379172823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8598511745372431586115215 12897767618058647379172823)
          ·
            refine ⟨19346651427087971068759235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12897767618058647379172823 19346651427087971068759235)
            ·
              refine ⟨29019977140631956603138853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19346651427087971068759235 29019977140631956603138853)
              ·
                refine ⟨5441245713868491863088535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29019977140631956603138853 5441245713868491863088535)
                ·
                  refine ⟨8161868570802737794632803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5441245713868491863088535 8161868570802737794632803)
                  ·
                    refine ⟨12242802856204106691949205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8161868570802737794632803 12242802856204106691949205)
                    ·
                      refine ⟨573881383884567501185119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12242802856204106691949205 573881383884567501185119)
                      ·
                        rfl

theorem cell23_1117630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1117630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117630 prefixEnd_1117630 := by exact prefixLift 1117630
  have htrace : WordTrace (prefixWord ++ tailWord_1117630) baseStart_1117630 baseEnd_1117630 := by
    simpa [prefixWord, tailWord_1117630, baseEnd_1117630] using wordTrace_append hprefix tailTrace_1117630
  have hstable : (prefixWord ++ tailWord_1117630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117630).length < 2 ^ (prefixWord ++ tailWord_1117630).sum := by decide
  have hdescent : baseEnd_1117630 < baseStart_1117630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117657 : List Nat := [1, 2, 1, 2, 4, 4, 2, 7]
def baseStart_1117657 : Nat := 118140960795 + 1117657 * 2 ^ 59
def prefixEnd_1117657 : Nat := 4983230072969 + 3 ^ 40 * 1117657 * 2
def baseEnd_1117657 : Nat := 21255379550453292427685

theorem tailTrace_1117657 : CollatzResearch.WordTrace tailWord_1117657 prefixEnd_1117657 21255379550453292427685 := by
  unfold tailWord_1117657
  simp only [CollatzResearch.WordTrace]
  refine ⟨40764299711927044463927225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27176199807951362975951483 40764299711927044463927225)
  ·
    refine ⟨30573224783945283347945419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40764299711927044463927225 30573224783945283347945419)
    ·
      refine ⟨45859837175917925021918129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30573224783945283347945419 45859837175917925021918129)
      ·
        refine ⟨34394877881938443766438597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45859837175917925021918129 34394877881938443766438597)
        ·
          refine ⟨6449039602863458206207237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34394877881938443766438597 6449039602863458206207237)
          ·
            refine ⟨1209194925536898413663857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6449039602863458206207237 1209194925536898413663857)
            ·
              refine ⟨906896194152673810247893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209194925536898413663857 906896194152673810247893)
              ·
                refine ⟨21255379550453292427685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 906896194152673810247893 21255379550453292427685)
                ·
                  rfl

theorem cell23_1117657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 7].length) (baseStart_1117657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117657 prefixEnd_1117657 := by exact prefixLift 1117657
  have htrace : WordTrace (prefixWord ++ tailWord_1117657) baseStart_1117657 baseEnd_1117657 := by
    simpa [prefixWord, tailWord_1117657, baseEnd_1117657] using wordTrace_append hprefix tailTrace_1117657
  have hstable : (prefixWord ++ tailWord_1117657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117657).length < 2 ^ (prefixWord ++ tailWord_1117657).sum := by decide
  have hdescent : baseEnd_1117657 < baseStart_1117657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117690 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_1117690 : Nat := 118140960795 + 1117690 * 2 ^ 59
def prefixEnd_1117690 : Nat := 4983230072969 + 3 ^ 40 * 1117690 * 2
def baseEnd_1117690 : Nat := 573912192723837266434843

theorem tailTrace_1117690 : CollatzResearch.WordTrace tailWord_1117690 prefixEnd_1117690 573912192723837266434843 := by
  unfold tailWord_1117690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10191375830201872774969631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27177002213871660733252349 10191375830201872774969631)
  ·
    refine ⟨15287063745302809162454447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10191375830201872774969631 15287063745302809162454447)
    ·
      refine ⟨22930595617954213743681671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15287063745302809162454447 22930595617954213743681671)
      ·
        refine ⟨34395893426931320615522507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22930595617954213743681671 34395893426931320615522507)
        ·
          refine ⟨51593840140396980923283761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34395893426931320615522507 51593840140396980923283761)
          ·
            refine ⟨38695380105297735692462821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51593840140396980923283761 38695380105297735692462821)
            ·
              refine ⟨7255383769743325442336779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38695380105297735692462821 7255383769743325442336779)
              ·
                refine ⟨10883075654614988163505169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7255383769743325442336779 10883075654614988163505169)
                ·
                  refine ⟨8162306740961241122628877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10883075654614988163505169 8162306740961241122628877)
                  ·
                    refine ⟨3060865027860465420985829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8162306740961241122628877 3060865027860465420985829)
                    ·
                      refine ⟨573912192723837266434843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3060865027860465420985829 573912192723837266434843)
                      ·
                        rfl

theorem cell23_1117690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_1117690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117690 prefixEnd_1117690 := by exact prefixLift 1117690
  have htrace : WordTrace (prefixWord ++ tailWord_1117690) baseStart_1117690 baseEnd_1117690 := by
    simpa [prefixWord, tailWord_1117690, baseEnd_1117690] using wordTrace_append hprefix tailTrace_1117690
  have hstable : (prefixWord ++ tailWord_1117690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117690).length < 2 ^ (prefixWord ++ tailWord_1117690).sum := by decide
  have hdescent : baseEnd_1117690 < baseStart_1117690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117702 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_1117702 : Nat := 118140960795 + 1117702 * 2 ^ 59
def prefixEnd_1117702 : Nat := 4983230072969 + 3 ^ 40 * 1117702 * 2
def baseEnd_1117702 : Nat := 573918354491691219484789

theorem tailTrace_1117702 : CollatzResearch.WordTrace tailWord_1117702 prefixEnd_1117702 573918354491691219484789 := by
  unfold tailWord_1117702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273935656148875535916105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27177293997842678099543573 1273935656148875535916105)
  ·
    refine ⟨955451742111656651937079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1273935656148875535916105 955451742111656651937079)
    ·
      refine ⟨1433177613167484977905619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955451742111656651937079 1433177613167484977905619)
      ·
        refine ⟨2149766419751227466858429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433177613167484977905619 2149766419751227466858429)
        ·
          refine ⟨806162407406710300071911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2149766419751227466858429 806162407406710300071911)
          ·
            refine ⟨1209243611110065450107867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806162407406710300071911 1209243611110065450107867)
            ·
              refine ⟨1813865416665098175161801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209243611110065450107867 1813865416665098175161801)
              ·
                refine ⟨1360399062498823631371351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1813865416665098175161801 1360399062498823631371351)
                ·
                  refine ⟨2040598593748235447057027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360399062498823631371351 2040598593748235447057027)
                  ·
                    refine ⟨3060897890622353170585541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040598593748235447057027 3060897890622353170585541)
                    ·
                      refine ⟨573918354491691219484789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3060897890622353170585541 573918354491691219484789)
                      ·
                        rfl

theorem cell23_1117702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_1117702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117702 prefixEnd_1117702 := by exact prefixLift 1117702
  have htrace : WordTrace (prefixWord ++ tailWord_1117702) baseStart_1117702 baseEnd_1117702 := by
    simpa [prefixWord, tailWord_1117702, baseEnd_1117702] using wordTrace_append hprefix tailTrace_1117702
  have hstable : (prefixWord ++ tailWord_1117702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117702).length < 2 ^ (prefixWord ++ tailWord_1117702).sum := by decide
  have hdescent : baseEnd_1117702 < baseStart_1117702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117724 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_1117724 : Nat := 118140960795 + 1117724 * 2 ^ 59
def prefixEnd_1117724 : Nat := 4983230072969 + 3 ^ 40 * 1117724 * 2
def baseEnd_1117724 : Nat := 573929651066090133409687

theorem tailTrace_1117724 : CollatzResearch.WordTrace tailWord_1117724 prefixEnd_1117724 573929651066090133409687 := by
  unfold tailWord_1117724
  simp only [CollatzResearch.WordTrace]
  refine ⟨20383371701342157453308113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27177828935122876604410817 20383371701342157453308113)
  ·
    refine ⟨15287528776006618089981085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20383371701342157453308113 15287528776006618089981085)
    ·
      refine ⟨5732823291002481783742907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15287528776006618089981085 5732823291002481783742907)
      ·
        refine ⟨8599234936503722675614361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5732823291002481783742907 8599234936503722675614361)
        ·
          refine ⟨6449426202377792006710771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8599234936503722675614361 6449426202377792006710771)
          ·
            refine ⟨9674139303566688010066157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6449426202377792006710771 9674139303566688010066157)
            ·
              refine ⟨3627802238837508003774809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9674139303566688010066157 3627802238837508003774809)
              ·
                refine ⟨2720851679128131002831107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3627802238837508003774809 2720851679128131002831107)
                ·
                  refine ⟨4081277518692196504246661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720851679128131002831107 4081277518692196504246661)
                  ·
                    refine ⟨765239534754786844546249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4081277518692196504246661 765239534754786844546249)
                    ·
                      refine ⟨573929651066090133409687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765239534754786844546249 573929651066090133409687)
                      ·
                        rfl

theorem cell23_1117724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_1117724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117724 prefixEnd_1117724 := by exact prefixLift 1117724
  have htrace : WordTrace (prefixWord ++ tailWord_1117724) baseStart_1117724 baseEnd_1117724 := by
    simpa [prefixWord, tailWord_1117724, baseEnd_1117724] using wordTrace_append hprefix tailTrace_1117724
  have hstable : (prefixWord ++ tailWord_1117724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117724).length < 2 ^ (prefixWord ++ tailWord_1117724).sum := by decide
  have hdescent : baseEnd_1117724 < baseStart_1117724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117728 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1117728 : Nat := 118140960795 + 1117728 * 2 ^ 59
def prefixEnd_1117728 : Nat := 4983230072969 + 3 ^ 40 * 1117728 * 2
def baseEnd_1117728 : Nat := 573931704988708117759669

theorem tailTrace_1117728 : CollatzResearch.WordTrace tailWord_1117728 prefixEnd_1117728 573931704988708117759669 := by
  unfold tailWord_1117728
  simp only [CollatzResearch.WordTrace]
  refine ⟨20383444647334911794880919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27177926196446549059841225 20383444647334911794880919)
  ·
    refine ⟨30575166971002367692321379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20383444647334911794880919 30575166971002367692321379)
    ·
      refine ⟨45862750456503551538482069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30575166971002367692321379 45862750456503551538482069)
      ·
        refine ⟨2149816427648603978366347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45862750456503551538482069 2149816427648603978366347)
        ·
          refine ⟨3224724641472905967549521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149816427648603978366347 3224724641472905967549521)
          ·
            refine ⟨2418543481104679475662141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3224724641472905967549521 2418543481104679475662141)
            ·
              refine ⟨906953805414254803373303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2418543481104679475662141 906953805414254803373303)
              ·
                refine ⟨1360430708121382205059955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906953805414254803373303 1360430708121382205059955)
                ·
                  refine ⟨2040646062182073307589933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360430708121382205059955 2040646062182073307589933)
                  ·
                    refine ⟨765242273318277490346225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040646062182073307589933 765242273318277490346225)
                    ·
                      refine ⟨573931704988708117759669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765242273318277490346225 573931704988708117759669)
                      ·
                        rfl

theorem cell23_1117728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1117728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117728 prefixEnd_1117728 := by exact prefixLift 1117728
  have htrace : WordTrace (prefixWord ++ tailWord_1117728) baseStart_1117728 baseEnd_1117728 := by
    simpa [prefixWord, tailWord_1117728, baseEnd_1117728] using wordTrace_append hprefix tailTrace_1117728
  have hstable : (prefixWord ++ tailWord_1117728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117728).length < 2 ^ (prefixWord ++ tailWord_1117728).sum := by decide
  have hdescent : baseEnd_1117728 < baseStart_1117728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117760 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 1, 7]
def baseStart_1117760 : Nat := 118140960795 + 1117760 * 2 ^ 59
def prefixEnd_1117760 : Nat := 4983230072969 + 3 ^ 40 * 1117760 * 2
def baseEnd_1117760 : Nat := 191316045456550664186507

theorem tailTrace_1117760 : CollatzResearch.WordTrace tailWord_1117760 prefixEnd_1117760 191316045456550664186507 := by
  unfold tailWord_1117760
  simp only [CollatzResearch.WordTrace]
  refine ⟨20384028215276946527463367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27178704287035928703284489 20384028215276946527463367)
  ·
    refine ⟨30576042322915419791195051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20384028215276946527463367 30576042322915419791195051)
    ·
      refine ⟨45864063484373129686792577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30576042322915419791195051 45864063484373129686792577)
      ·
        refine ⟨34398047613279847265094433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45864063484373129686792577 34398047613279847265094433)
        ·
          refine ⟨25798535709959885448820825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34398047613279847265094433 25798535709959885448820825)
          ·
            refine ⟨19348901782469914086615619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25798535709959885448820825 19348901782469914086615619)
            ·
              refine ⟨29023352673704871129923429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19348901782469914086615619 29023352673704871129923429)
              ·
                refine ⟨5441878626319663336860643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29023352673704871129923429 5441878626319663336860643)
                ·
                  refine ⟨8162817939479495005290965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5441878626319663336860643 8162817939479495005290965)
                  ·
                    refine ⟨191316045456550664186507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8162817939479495005290965 191316045456550664186507)
                    ·
                      rfl

theorem cell23_1117760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_1117760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117760 prefixEnd_1117760 := by exact prefixLift 1117760
  have htrace : WordTrace (prefixWord ++ tailWord_1117760) baseStart_1117760 baseEnd_1117760 := by
    simpa [prefixWord, tailWord_1117760, baseEnd_1117760] using wordTrace_append hprefix tailTrace_1117760
  have hstable : (prefixWord ++ tailWord_1117760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117760).length < 2 ^ (prefixWord ++ tailWord_1117760).sum := by decide
  have hdescent : baseEnd_1117760 < baseStart_1117760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117814 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1117814 : Nat := 118140960795 + 1117814 * 2 ^ 59
def prefixEnd_1117814 : Nat := 4983230072969 + 3 ^ 40 * 1117814 * 2
def baseEnd_1117814 : Nat := 573975864324994781284273

theorem tailTrace_1117814 : CollatzResearch.WordTrace tailWord_1117814 prefixEnd_1117814 573975864324994781284273 := by
  unfold tailWord_1117814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548126623272391267337031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27180017314905506851594997 2548126623272391267337031)
  ·
    refine ⟨3822189934908586901005547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2548126623272391267337031 3822189934908586901005547)
    ·
      refine ⟨5733284902362880351508321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822189934908586901005547 5733284902362880351508321)
      ·
        refine ⟨4299963676772160263631241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5733284902362880351508321 4299963676772160263631241)
        ·
          refine ⟨3224972757579120197723431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4299963676772160263631241 3224972757579120197723431)
          ·
            refine ⟨4837459136368680296585147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224972757579120197723431 4837459136368680296585147)
            ·
              refine ⟨7256188704553020444877721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4837459136368680296585147 7256188704553020444877721)
              ·
                refine ⟨5442141528414765333658291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7256188704553020444877721 5442141528414765333658291)
                ·
                  refine ⟨8163212292622148000487437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5442141528414765333658291 8163212292622148000487437)
                  ·
                    refine ⟨3061204609733305500182789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8163212292622148000487437 3061204609733305500182789)
                    ·
                      refine ⟨573975864324994781284273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3061204609733305500182789 573975864324994781284273)
                      ·
                        rfl

theorem cell23_1117814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1117814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117814 prefixEnd_1117814 := by exact prefixLift 1117814
  have htrace : WordTrace (prefixWord ++ tailWord_1117814) baseStart_1117814 baseEnd_1117814 := by
    simpa [prefixWord, tailWord_1117814, baseEnd_1117814] using wordTrace_append hprefix tailTrace_1117814
  have hstable : (prefixWord ++ tailWord_1117814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117814).length < 2 ^ (prefixWord ++ tailWord_1117814).sum := by decide
  have hdescent : baseEnd_1117814 < baseStart_1117814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117817 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 3]
def baseStart_1117817 : Nat := 118140960795 + 1117817 * 2 ^ 59
def prefixEnd_1117817 : Nat := 4983230072969 + 3 ^ 40 * 1117817 * 2
def baseEnd_1117817 : Nat := 573977404766958269546759

theorem tailTrace_1117817 : CollatzResearch.WordTrace tailWord_1117817 prefixEnd_1117817 573977404766958269546759 := by
  unfold tailWord_1117817
  simp only [CollatzResearch.WordTrace]
  refine ⟨40770135391347391789751705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27180090260898261193167803 40770135391347391789751705)
  ·
    refine ⟨30577601543510543842313779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40770135391347391789751705 30577601543510543842313779)
    ·
      refine ⟨45866402315265815763470669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30577601543510543842313779 45866402315265815763470669)
      ·
        refine ⟨17199900868224680911301501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45866402315265815763470669 17199900868224680911301501)
        ·
          refine ⟨6449962825584255341738063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17199900868224680911301501 6449962825584255341738063)
          ·
            refine ⟨9674944238376383012607095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6449962825584255341738063 9674944238376383012607095)
            ·
              refine ⟨14512416357564574518910643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9674944238376383012607095 14512416357564574518910643)
              ·
                refine ⟨21768624536346861778365965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14512416357564574518910643 21768624536346861778365965)
                ·
                  refine ⟨8163234201130073166887237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21768624536346861778365965 8163234201130073166887237)
                  ·
                    refine ⟨1530606412711888718791357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8163234201130073166887237 1530606412711888718791357)
                    ·
                      refine ⟨573977404766958269546759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1530606412711888718791357 573977404766958269546759)
                      ·
                        rfl

theorem cell23_1117817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_1117817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117817 prefixEnd_1117817 := by exact prefixLift 1117817
  have htrace : WordTrace (prefixWord ++ tailWord_1117817) baseStart_1117817 baseEnd_1117817 := by
    simpa [prefixWord, tailWord_1117817, baseEnd_1117817] using wordTrace_append hprefix tailTrace_1117817
  have hstable : (prefixWord ++ tailWord_1117817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117817).length < 2 ^ (prefixWord ++ tailWord_1117817).sum := by decide
  have hdescent : baseEnd_1117817 < baseStart_1117817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117834 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1117834 : Nat := 118140960795 + 1117834 * 2 ^ 59
def prefixEnd_1117834 : Nat := 4983230072969 + 3 ^ 40 * 1117834 * 2
def baseEnd_1117834 : Nat := 573986133938084703034181

theorem tailTrace_1117834 : CollatzResearch.WordTrace tailWord_1117834 prefixEnd_1117834 573986133938084703034181 := by
  unfold tailWord_1117834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10192688858071450923280139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27180503621523869128747037 10192688858071450923280139)
  ·
    refine ⟨15289033287107176384920209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10192688858071450923280139 15289033287107176384920209)
    ·
      refine ⟨11466774965330382288690157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15289033287107176384920209 11466774965330382288690157)
      ·
        refine ⟨4300040611998893358258809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11466774965330382288690157 4300040611998893358258809)
        ·
          refine ⟨3225030458999170018694107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4300040611998893358258809 3225030458999170018694107)
          ·
            refine ⟨4837545688498755028041161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3225030458999170018694107 4837545688498755028041161)
            ·
              refine ⟨3628159266374066271030871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4837545688498755028041161 3628159266374066271030871)
              ·
                refine ⟨5442238899561099406546307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628159266374066271030871 5442238899561099406546307)
                ·
                  refine ⟨8163358349341649109819461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5442238899561099406546307 8163358349341649109819461)
                  ·
                    refine ⟨1530629690501559208091149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8163358349341649109819461 1530629690501559208091149)
                    ·
                      refine ⟨573986133938084703034181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1530629690501559208091149 573986133938084703034181)
                      ·
                        rfl

theorem cell23_1117834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1117834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117834 prefixEnd_1117834 := by exact prefixLift 1117834
  have htrace : WordTrace (prefixWord ++ tailWord_1117834) baseStart_1117834 baseEnd_1117834 := by
    simpa [prefixWord, tailWord_1117834, baseEnd_1117834] using wordTrace_append hprefix tailTrace_1117834
  have hstable : (prefixWord ++ tailWord_1117834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117834).length < 2 ^ (prefixWord ++ tailWord_1117834).sum := by decide
  have hdescent : baseEnd_1117834 < baseStart_1117834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117854 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_1117854 : Nat := 118140960795 + 1117854 * 2 ^ 59
def prefixEnd_1117854 : Nat := 4983230072969 + 3 ^ 40 * 1117854 * 2
def baseEnd_1117854 : Nat := 63777378172352736087121

theorem tailTrace_1117854 : CollatzResearch.WordTrace tailWord_1117854 prefixEnd_1117854 63777378172352736087121 := by
  unfold tailWord_1117854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5096435611526668388606077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27180989928142231405899077 5096435611526668388606077)
  ·
    refine ⟨1911163354322500645727279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5096435611526668388606077 1911163354322500645727279)
    ·
      refine ⟨2866745031483750968590919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1911163354322500645727279 2866745031483750968590919)
      ·
        refine ⟨4300117547225626452886379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2866745031483750968590919 4300117547225626452886379)
        ·
          refine ⟨6450176320838439679329569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300117547225626452886379 6450176320838439679329569)
          ·
            refine ⟨4837632240628829759497177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6450176320838439679329569 4837632240628829759497177)
            ·
              refine ⟨3628224180471622319622883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4837632240628829759497177 3628224180471622319622883)
              ·
                refine ⟨5442336270707433479434325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628224180471622319622883 5442336270707433479434325)
                ·
                  refine ⟨63777378172352736087121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5442336270707433479434325 63777378172352736087121)
                  ·
                    rfl

theorem cell23_1117854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_1117854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117854 prefixEnd_1117854 := by exact prefixLift 1117854
  have htrace : WordTrace (prefixWord ++ tailWord_1117854) baseStart_1117854 baseEnd_1117854 := by
    simpa [prefixWord, tailWord_1117854, baseEnd_1117854] using wordTrace_append hprefix tailTrace_1117854
  have hstable : (prefixWord ++ tailWord_1117854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117854).length < 2 ^ (prefixWord ++ tailWord_1117854).sum := by decide
  have hdescent : baseEnd_1117854 < baseStart_1117854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117874 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_1117874 : Nat := 118140960795 + 1117874 * 2 ^ 59
def prefixEnd_1117874 : Nat := 4983230072969 + 3 ^ 40 * 1117874 * 2
def baseEnd_1117874 : Nat := 574006673164264546533997

theorem tailTrace_1117874 : CollatzResearch.WordTrace tailWord_1117874 prefixEnd_1117874 574006673164264546533997 := by
  unfold tailWord_1117874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10193053588035222631144169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27181476234760593683051117 10193053588035222631144169)
  ·
    refine ⟨7644790191026416973358127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10193053588035222631144169 7644790191026416973358127)
    ·
      refine ⟨11467185286539625460037191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7644790191026416973358127 11467185286539625460037191)
      ·
        refine ⟨17200777929809438190055787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11467185286539625460037191 17200777929809438190055787)
        ·
          refine ⟨25801166894714157285083681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17200777929809438190055787 25801166894714157285083681)
          ·
            refine ⟨19350875171035617963812761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25801166894714157285083681 19350875171035617963812761)
            ·
              refine ⟨14513156378276713472859571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19350875171035617963812761 14513156378276713472859571)
              ·
                refine ⟨21769734567415070209289357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14513156378276713472859571 21769734567415070209289357)
                ·
                  refine ⟨8163650462780651328483509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21769734567415070209289357 8163650462780651328483509)
                  ·
                    refine ⟨765342230885686062045329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8163650462780651328483509 765342230885686062045329)
                    ·
                      refine ⟨574006673164264546533997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765342230885686062045329 574006673164264546533997)
                      ·
                        rfl

theorem cell23_1117874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_1117874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117874 prefixEnd_1117874 := by exact prefixLift 1117874
  have htrace : WordTrace (prefixWord ++ tailWord_1117874) baseStart_1117874 baseEnd_1117874 := by
    simpa [prefixWord, tailWord_1117874, baseEnd_1117874] using wordTrace_append hprefix tailTrace_1117874
  have hstable : (prefixWord ++ tailWord_1117874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117874).length < 2 ^ (prefixWord ++ tailWord_1117874).sum := by decide
  have hdescent : baseEnd_1117874 < baseStart_1117874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117884 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_1117884 : Nat := 118140960795 + 1117884 * 2 ^ 59
def prefixEnd_1117884 : Nat := 4983230072969 + 3 ^ 40 * 1117884 * 2
def baseEnd_1117884 : Nat := 191337269323603169136317

theorem tailTrace_1117884 : CollatzResearch.WordTrace tailWord_1117884 prefixEnd_1117884 191337269323603169136317 := by
  unfold tailWord_1117884
  simp only [CollatzResearch.WordTrace]
  refine ⟨20386289541052331116220353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27181719388069774821627137 20386289541052331116220353)
  ·
    refine ⟨15289717155789248337165265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20386289541052331116220353 15289717155789248337165265)
    ·
      refine ⟨11467287866841936252873949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15289717155789248337165265 11467287866841936252873949)
      ·
        refine ⟨4300232950065726094827731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11467287866841936252873949 4300232950065726094827731)
        ·
          refine ⟨6450349425098589142241597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300232950065726094827731 6450349425098589142241597)
          ·
            refine ⟨2418881034411970928340599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6450349425098589142241597 2418881034411970928340599)
            ·
              refine ⟨3628321551617956392510899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418881034411970928340599 3628321551617956392510899)
              ·
                refine ⟨5442482327426934588766349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628321551617956392510899 5442482327426934588766349)
                ·
                  refine ⟨2040930872785100470787381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5442482327426934588766349 2040930872785100470787381)
                  ·
                    refine ⟨191337269323603169136317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2040930872785100470787381 191337269323603169136317)
                    ·
                      rfl

theorem cell23_1117884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_1117884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117884 prefixEnd_1117884 := by exact prefixLift 1117884
  have htrace : WordTrace (prefixWord ++ tailWord_1117884) baseStart_1117884 baseEnd_1117884 := by
    simpa [prefixWord, tailWord_1117884, baseEnd_1117884] using wordTrace_append hprefix tailTrace_1117884
  have hstable : (prefixWord ++ tailWord_1117884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117884).length < 2 ^ (prefixWord ++ tailWord_1117884).sum := by decide
  have hdescent : baseEnd_1117884 < baseStart_1117884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117907 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 3]
def baseStart_1117907 : Nat := 118140960795 + 1117907 * 2 ^ 59
def prefixEnd_1117907 : Nat := 4983230072969 + 3 ^ 40 * 1117907 * 2
def baseEnd_1117907 : Nat := 574023618025862917421345

theorem tailTrace_1117907 : CollatzResearch.WordTrace tailWord_1117907 prefixEnd_1117907 574023618025862917421345 := by
  unfold tailWord_1117907
  simp only [CollatzResearch.WordTrace]
  refine ⟨40773417961021337160527975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27182278640680891440351983 40773417961021337160527975)
  ·
    refine ⟨61160126941532005740791963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40773417961021337160527975 61160126941532005740791963)
    ·
      refine ⟨91740190412298008611187945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61160126941532005740791963 91740190412298008611187945)
      ·
        refine ⟨68805142809223506458390959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91740190412298008611187945 68805142809223506458390959)
        ·
          refine ⟨103207714213835259687586439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68805142809223506458390959 103207714213835259687586439)
          ·
            refine ⟨154811571320752889531379659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103207714213835259687586439 154811571320752889531379659)
            ·
              refine ⟨232217356981129334297069489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154811571320752889531379659 232217356981129334297069489)
              ·
                refine ⟨174163017735847000722802117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232217356981129334297069489 174163017735847000722802117)
                ·
                  refine ⟨32655565825471312635525397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174163017735847000722802117 32655565825471312635525397)
                  ·
                    refine ⟨1530729648068967779790253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32655565825471312635525397 1530729648068967779790253)
                    ·
                      refine ⟨574023618025862917421345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1530729648068967779790253 574023618025862917421345)
                      ·
                        rfl

theorem cell23_1117907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_1117907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117907 prefixEnd_1117907 := by exact prefixLift 1117907
  have htrace : WordTrace (prefixWord ++ tailWord_1117907) baseStart_1117907 baseEnd_1117907 := by
    simpa [prefixWord, tailWord_1117907, baseEnd_1117907] using wordTrace_append hprefix tailTrace_1117907
  have hstable : (prefixWord ++ tailWord_1117907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117907).length < 2 ^ (prefixWord ++ tailWord_1117907).sum := by decide
  have hdescent : baseEnd_1117907 < baseStart_1117907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117908 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1117908 : Nat := 118140960795 + 1117908 * 2 ^ 59
def prefixEnd_1117908 : Nat := 4983230072969 + 3 ^ 40 * 1117908 * 2
def baseEnd_1117908 : Nat := 574024131506517413508841

theorem tailTrace_1117908 : CollatzResearch.WordTrace tailWord_1117908 prefixEnd_1117908 574024131506517413508841 := by
  unfold tailWord_1117908
  simp only [CollatzResearch.WordTrace]
  refine ⟨20386727217008857165657189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27182302956011809554209585 20386727217008857165657189)
  ·
    refine ⟨3822511353189160718560723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20386727217008857165657189 3822511353189160718560723)
    ·
      refine ⟨5733767029783741077841085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822511353189160718560723 5733767029783741077841085)
      ·
        refine ⟨2150162636168902904190407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5733767029783741077841085 2150162636168902904190407)
        ·
          refine ⟨3225243954253354356285611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2150162636168902904190407 3225243954253354356285611)
          ·
            refine ⟨4837865931380031534428417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3225243954253354356285611 4837865931380031534428417)
            ·
              refine ⟨3628399448535023650821313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4837865931380031534428417 3628399448535023650821313)
              ·
                refine ⟨2721299586401267738115985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628399448535023650821313 2721299586401267738115985)
                ·
                  refine ⟨2040974689800950803586989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2721299586401267738115985 2040974689800950803586989)
                  ·
                    refine ⟨765365508675356551345121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040974689800950803586989 765365508675356551345121)
                    ·
                      refine ⟨574024131506517413508841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765365508675356551345121 574024131506517413508841)
                      ·
                        rfl

theorem cell23_1117908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1117908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117908 prefixEnd_1117908 := by exact prefixLift 1117908
  have htrace : WordTrace (prefixWord ++ tailWord_1117908) baseStart_1117908 baseEnd_1117908 := by
    simpa [prefixWord, tailWord_1117908, baseEnd_1117908] using wordTrace_append hprefix tailTrace_1117908
  have hstable : (prefixWord ++ tailWord_1117908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117908).length < 2 ^ (prefixWord ++ tailWord_1117908).sum := by decide
  have hdescent : baseEnd_1117908 < baseStart_1117908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117924 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_1117924 : Nat := 118140960795 + 1117924 * 2 ^ 59
def prefixEnd_1117924 : Nat := 4983230072969 + 3 ^ 40 * 1117924 * 2
def baseEnd_1117924 : Nat := 574032347196989350908767

theorem tailTrace_1117924 : CollatzResearch.WordTrace tailWord_1117924 prefixEnd_1117924 574032347196989350908767 := by
  unfold tailWord_1117924
  simp only [CollatzResearch.WordTrace]
  refine ⟨20387019000979874531948413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27182692001306499375931217 20387019000979874531948413)
  ·
    refine ⟨7645132125367452949480655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20387019000979874531948413 7645132125367452949480655)
    ·
      refine ⟨11467698188051179424220983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7645132125367452949480655 11467698188051179424220983)
      ·
        refine ⟨17201547282076769136331475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11467698188051179424220983 17201547282076769136331475)
        ·
          refine ⟨25802320923115153704497213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17201547282076769136331475 25802320923115153704497213)
          ·
            refine ⟨9675870346168182639186455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25802320923115153704497213 9675870346168182639186455)
            ·
              refine ⟨14513805519252273958779683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9675870346168182639186455 14513805519252273958779683)
              ·
                refine ⟨21770708278878410938169525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14513805519252273958779683 21770708278878410938169525)
                ·
                  refine ⟨2041003901144851025453393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21770708278878410938169525 2041003901144851025453393)
                  ·
                    refine ⟨1530752925858638269090045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2041003901144851025453393 1530752925858638269090045)
                    ·
                      refine ⟨574032347196989350908767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1530752925858638269090045 574032347196989350908767)
                      ·
                        rfl

theorem cell23_1117924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_1117924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117924 prefixEnd_1117924 := by exact prefixLift 1117924
  have htrace : WordTrace (prefixWord ++ tailWord_1117924) baseStart_1117924 baseEnd_1117924 := by
    simpa [prefixWord, tailWord_1117924, baseEnd_1117924] using wordTrace_append hprefix tailTrace_1117924
  have hstable : (prefixWord ++ tailWord_1117924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117924).length < 2 ^ (prefixWord ++ tailWord_1117924).sum := by decide
  have hdescent : baseEnd_1117924 < baseStart_1117924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117938 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_1117938 : Nat := 118140960795 + 1117938 * 2 ^ 59
def prefixEnd_1117938 : Nat := 4983230072969 + 3 ^ 40 * 1117938 * 2
def baseEnd_1117938 : Nat := 574039535926152296133703

theorem tailTrace_1117938 : CollatzResearch.WordTrace tailWord_1117938 prefixEnd_1117938 574039535926152296133703 := by
  unfold tailWord_1117938
  simp only [CollatzResearch.WordTrace]
  refine ⟨10193637155977257363726617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27183032415939352969937645 10193637155977257363726617)
  ·
    refine ⟨7645227866982943022794963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10193637155977257363726617 7645227866982943022794963)
    ·
      refine ⟨11467841800474414534192445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7645227866982943022794963 11467841800474414534192445)
      ·
        refine ⟨4300440675177905450322167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11467841800474414534192445 4300440675177905450322167)
        ·
          refine ⟨6450661012766858175483251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300440675177905450322167 6450661012766858175483251)
          ·
            refine ⟨9675991519150287263224877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450661012766858175483251 9675991519150287263224877)
            ·
              refine ⟨3628496819681357723709329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9675991519150287263224877 3628496819681357723709329)
              ·
                refine ⟨2721372614761018292781997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628496819681357723709329 2721372614761018292781997)
                ·
                  refine ⟨1020514730535381859793249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2721372614761018292781997 1020514730535381859793249)
                  ·
                    refine ⟨765386047901536394844937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1020514730535381859793249 765386047901536394844937)
                    ·
                      refine ⟨574039535926152296133703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765386047901536394844937 574039535926152296133703)
                      ·
                        rfl

theorem cell23_1117938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_1117938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117938 prefixEnd_1117938 := by exact prefixLift 1117938
  have htrace : WordTrace (prefixWord ++ tailWord_1117938) baseStart_1117938 baseEnd_1117938 := by
    simpa [prefixWord, tailWord_1117938, baseEnd_1117938] using wordTrace_append hprefix tailTrace_1117938
  have hstable : (prefixWord ++ tailWord_1117938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117938).length < 2 ^ (prefixWord ++ tailWord_1117938).sum := by decide
  have hdescent : baseEnd_1117938 < baseStart_1117938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117967 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_1117967 : Nat := 118140960795 + 1117967 * 2 ^ 59
def prefixEnd_1117967 : Nat := 4983230072969 + 3 ^ 40 * 1117967 * 2
def baseEnd_1117967 : Nat := 574054426865132682671069

theorem tailTrace_1117967 : CollatzResearch.WordTrace tailWord_1117967 prefixEnd_1117967 574054426865132682671069 := by
  unfold tailWord_1117967
  simp only [CollatzResearch.WordTrace]
  refine ⟨40775606340803967407712155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27183737560535978271808103 40775606340803967407712155)
  ·
    refine ⟨61163409511205951111568233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40775606340803967407712155 61163409511205951111568233)
    ·
      refine ⟨45872557133404463333676175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61163409511205951111568233 45872557133404463333676175)
      ·
        refine ⟨68808835700106695000514263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45872557133404463333676175 68808835700106695000514263)
        ·
          refine ⟨103213253550160042500771395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68808835700106695000514263 103213253550160042500771395)
          ·
            refine ⟨154819880325240063751157093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103213253550160042500771395 154819880325240063751157093)
            ·
              refine ⟨29028727560982511953341955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154819880325240063751157093 29028727560982511953341955)
              ·
                refine ⟨43543091341473767930012933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29028727560982511953341955 43543091341473767930012933)
                ·
                  refine ⟨8164329626526331486877425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43543091341473767930012933 8164329626526331486877425)
                  ·
                    refine ⟨6123247219894748615158069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8164329626526331486877425 6123247219894748615158069)
                    ·
                      refine ⟨574054426865132682671069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6123247219894748615158069 574054426865132682671069)
                      ·
                        rfl

theorem cell23_1117967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_1117967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117967 prefixEnd_1117967 := by exact prefixLift 1117967
  have htrace : WordTrace (prefixWord ++ tailWord_1117967) baseStart_1117967 baseEnd_1117967 := by
    simpa [prefixWord, tailWord_1117967, baseEnd_1117967] using wordTrace_append hprefix tailTrace_1117967
  have hstable : (prefixWord ++ tailWord_1117967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117967).length < 2 ^ (prefixWord ++ tailWord_1117967).sum := by decide
  have hdescent : baseEnd_1117967 < baseStart_1117967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117971 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 3]
def baseStart_1117971 : Nat := 118140960795 + 1117971 * 2 ^ 59
def prefixEnd_1117971 : Nat := 4983230072969 + 3 ^ 40 * 1117971 * 2
def baseEnd_1117971 : Nat := 574056480787750667021051

theorem tailTrace_1117971 : CollatzResearch.WordTrace tailWord_1117971 prefixEnd_1117971 574056480787750667021051 := by
  unfold tailWord_1117971
  simp only [CollatzResearch.WordTrace]
  refine ⟨40775752232789476090857767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27183834821859650727238511 40775752232789476090857767)
  ·
    refine ⟨61163628349184214136286651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40775752232789476090857767 61163628349184214136286651)
    ·
      refine ⟨91745442523776321204429977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61163628349184214136286651 91745442523776321204429977)
      ·
        refine ⟨68809081892832240903322483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91745442523776321204429977 68809081892832240903322483)
        ·
          refine ⟨103213622839248361354983725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68809081892832240903322483 103213622839248361354983725)
          ·
            refine ⟨38705108564718135508118897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103213622839248361354983725 38705108564718135508118897)
            ·
              refine ⟨29028831423538601631089173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38705108564718135508118897 29028831423538601631089173)
              ·
                refine ⟨1360726472978371951457305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29028831423538601631089173 1360726472978371951457305)
                ·
                  refine ⟨1020544854733778963592979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360726472978371951457305 1020544854733778963592979)
                  ·
                    refine ⟨1530817282100668445389469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1020544854733778963592979 1530817282100668445389469)
                    ·
                      refine ⟨574056480787750667021051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1530817282100668445389469 574056480787750667021051)
                      ·
                        rfl

theorem cell23_1117971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 3].length) (baseStart_1117971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117971 prefixEnd_1117971 := by exact prefixLift 1117971
  have htrace : WordTrace (prefixWord ++ tailWord_1117971) baseStart_1117971 baseEnd_1117971 := by
    simpa [prefixWord, tailWord_1117971, baseEnd_1117971] using wordTrace_append hprefix tailTrace_1117971
  have hstable : (prefixWord ++ tailWord_1117971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117971).length < 2 ^ (prefixWord ++ tailWord_1117971).sum := by decide
  have hdescent : baseEnd_1117971 < baseStart_1117971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117982 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1117982 : Nat := 118140960795 + 1117982 * 2 ^ 59
def prefixEnd_1117982 : Nat := 4983230072969 + 3 ^ 40 * 1117982 * 2
def baseEnd_1117982 : Nat := 191354043024983374661167

theorem tailTrace_1117982 : CollatzResearch.WordTrace tailWord_1117982 prefixEnd_1117982 191354043024983374661167 := by
  unfold tailWord_1117982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097019179468703121188525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27184102290499749979672133 5097019179468703121188525)
  ·
    refine ⟨1911382192300763670445697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5097019179468703121188525 1911382192300763670445697)
    ·
      refine ⟨1433536644225572752834273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1911382192300763670445697 1433536644225572752834273)
      ·
        refine ⟨1075152483169179564625705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1433536644225572752834273 1075152483169179564625705)
        ·
          refine ⟨806364362376884673469279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075152483169179564625705 806364362376884673469279)
          ·
            refine ⟨1209546543565327010203919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806364362376884673469279 1209546543565327010203919)
            ·
              refine ⟨1814319815347990515305879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209546543565327010203919 1814319815347990515305879)
              ·
                refine ⟨2721479723021985772958819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814319815347990515305879 2721479723021985772958819)
                ·
                  refine ⟨4082219584532978659438229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721479723021985772958819 4082219584532978659438229)
                  ·
                    refine ⟨191354043024983374661167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4082219584532978659438229 191354043024983374661167)
                    ·
                      rfl

theorem cell23_1117982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1117982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117982 prefixEnd_1117982 := by exact prefixLift 1117982
  have htrace : WordTrace (prefixWord ++ tailWord_1117982) baseStart_1117982 baseEnd_1117982 := by
    simpa [prefixWord, tailWord_1117982, baseEnd_1117982] using wordTrace_append hprefix tailTrace_1117982
  have hstable : (prefixWord ++ tailWord_1117982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117982).length < 2 ^ (prefixWord ++ tailWord_1117982).sum := by decide
  have hdescent : baseEnd_1117982 < baseStart_1117982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117988 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1117988 : Nat := 118140960795 + 1117988 * 2 ^ 59
def prefixEnd_1117988 : Nat := 4983230072969 + 3 ^ 40 * 1117988 * 2
def baseEnd_1117988 : Nat := 574065209958877100508473

theorem tailTrace_1117988 : CollatzResearch.WordTrace tailWord_1117988 prefixEnd_1117988 574065209958877100508473 := by
  unfold tailWord_1117988
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388186136863943997113309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27184248182485258662817745 20388186136863943997113309)
  ·
    refine ⟨7645569801323978998917491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20388186136863943997113309 7645569801323978998917491)
    ·
      refine ⟨11468354701985968498376237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7645569801323978998917491 11468354701985968498376237)
      ·
        refine ⟨4300633013244738186891089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11468354701985968498376237 4300633013244738186891089)
        ·
          refine ⟨3225474759933553640168317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4300633013244738186891089 3225474759933553640168317)
          ·
            refine ⟨1209553034975082615063119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3225474759933553640168317 1209553034975082615063119)
            ·
              refine ⟨1814329552462623922594679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209553034975082615063119 1814329552462623922594679)
              ·
                refine ⟨2721494328693935883892019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814329552462623922594679 2721494328693935883892019)
                ·
                  refine ⟨4082241493040903825838029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721494328693935883892019 4082241493040903825838029)
                  ·
                    refine ⟨1530840559890338934689261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4082241493040903825838029 1530840559890338934689261)
                    ·
                      refine ⟨574065209958877100508473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1530840559890338934689261 574065209958877100508473)
                      ·
                        rfl

theorem cell23_1117988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1117988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1117988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1117988 prefixEnd_1117988 := by exact prefixLift 1117988
  have htrace : WordTrace (prefixWord ++ tailWord_1117988) baseStart_1117988 baseEnd_1117988 := by
    simpa [prefixWord, tailWord_1117988, baseEnd_1117988] using wordTrace_append hprefix tailTrace_1117988
  have hstable : (prefixWord ++ tailWord_1117988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117988).length < 2 ^ (prefixWord ++ tailWord_1117988).sum := by decide
  have hdescent : baseEnd_1117988 < baseStart_1117988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118074 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_1118074 : Nat := 118140960795 + 1118074 * 2 ^ 59
def prefixEnd_1118074 : Nat := 4983230072969 + 3 ^ 40 * 1118074 * 2
def baseEnd_1118074 : Nat := 574109369295163764033077

theorem tailTrace_1118074 : CollatzResearch.WordTrace tailWord_1118074 prefixEnd_1118074 574109369295163764033077 := by
  unfold tailWord_1118074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10194877237854081170464319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27186339300944216454571517 10194877237854081170464319)
  ·
    refine ⟨15292315856781121755696479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10194877237854081170464319 15292315856781121755696479)
    ·
      refine ⟨22938473785171682633544719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15292315856781121755696479 22938473785171682633544719)
      ·
        refine ⟨34407710677757523950317079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22938473785171682633544719 34407710677757523950317079)
        ·
          refine ⟨51611566016636285925475619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34407710677757523950317079 51611566016636285925475619)
          ·
            refine ⟨77417349024954428888213429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51611566016636285925475619 77417349024954428888213429)
            ·
              refine ⟨7257876471089477708270009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77417349024954428888213429 7257876471089477708270009)
              ·
                refine ⟨5443407353317108281202507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7257876471089477708270009 5443407353317108281202507)
                ·
                  refine ⟨8165111029975662421803761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5443407353317108281202507 8165111029975662421803761)
                  ·
                    refine ⟨6123833272481746816352821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8165111029975662421803761 6123833272481746816352821)
                    ·
                      refine ⟨574109369295163764033077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6123833272481746816352821 574109369295163764033077)
                      ·
                        rfl

theorem cell23_1118074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_1118074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118074 prefixEnd_1118074 := by exact prefixLift 1118074
  have htrace : WordTrace (prefixWord ++ tailWord_1118074) baseStart_1118074 baseEnd_1118074 := by
    simpa [prefixWord, tailWord_1118074, baseEnd_1118074] using wordTrace_append hprefix tailTrace_1118074
  have hstable : (prefixWord ++ tailWord_1118074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118074).length < 2 ^ (prefixWord ++ tailWord_1118074).sum := by decide
  have hdescent : baseEnd_1118074 < baseStart_1118074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118121 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 3]
def baseStart_1118121 : Nat := 118140960795 + 1118121 * 2 ^ 59
def prefixEnd_1118121 : Nat := 4983230072969 + 3 ^ 40 * 1118121 * 2
def baseEnd_1118121 : Nat := 574133502885925080145361

theorem tailTrace_1118121 : CollatzResearch.WordTrace tailWord_1118121 prefixEnd_1118121 574133502885925080145361 := by
  unfold tailWord_1118121
  simp only [CollatzResearch.WordTrace]
  refine ⟨40781223182246051708818217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27187482121497367805878811 40781223182246051708818217)
  ·
    refine ⟨30585917386684538781613663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40781223182246051708818217 30585917386684538781613663)
    ·
      refine ⟨45878876080026808172420495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30585917386684538781613663 45878876080026808172420495)
      ·
        refine ⟨68818314120040212258630743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45878876080026808172420495 68818314120040212258630743)
        ·
          refine ⟨103227471180060318387946115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68818314120040212258630743 103227471180060318387946115)
          ·
            refine ⟨154841206770090477581919173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103227471180060318387946115 154841206770090477581919173)
            ·
              refine ⟨29032726269391964546609845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154841206770090477581919173 29032726269391964546609845)
              ·
                refine ⟨2721818087755496676244673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29032726269391964546609845 2721818087755496676244673)
                ·
                  refine ⟨2041363565816622507183505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2721818087755496676244673 2041363565816622507183505)
                  ·
                    refine ⟨1531022674362466880387629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2041363565816622507183505 1531022674362466880387629)
                    ·
                      refine ⟨574133502885925080145361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1531022674362466880387629 574133502885925080145361)
                      ·
                        rfl

theorem cell23_1118121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_1118121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118121 prefixEnd_1118121 := by exact prefixLift 1118121
  have htrace : WordTrace (prefixWord ++ tailWord_1118121) baseStart_1118121 baseEnd_1118121 := by
    simpa [prefixWord, tailWord_1118121, baseEnd_1118121] using wordTrace_append hprefix tailTrace_1118121
  have hstable : (prefixWord ++ tailWord_1118121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118121).length < 2 ^ (prefixWord ++ tailWord_1118121).sum := by decide
  have hdescent : baseEnd_1118121 < baseStart_1118121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118141 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 8]
def baseStart_1118141 : Nat := 118140960795 + 1118141 * 2 ^ 59
def prefixEnd_1118141 : Nat := 4983230072969 + 3 ^ 40 * 1118141 * 2
def baseEnd_1118141 : Nat := 63793752499890555766141

theorem tailTrace_1118141 : CollatzResearch.WordTrace tailWord_1118141 prefixEnd_1118141 63793752499890555766141 := by
  unfold tailWord_1118141
  simp only [CollatzResearch.WordTrace]
  refine ⟨40781952642173595124546277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27187968428115730083030851 40781952642173595124546277)
  ·
    refine ⟨7646616120407549085852427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40781952642173595124546277 7646616120407549085852427)
    ·
      refine ⟨11469924180611323628778641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7646616120407549085852427 11469924180611323628778641)
      ·
        refine ⟨8602443135458492721583981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11469924180611323628778641 8602443135458492721583981)
        ·
          refine ⟨3225916175796934770593993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8602443135458492721583981 3225916175796934770593993)
          ·
            refine ⟨2419437131847701077945495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3225916175796934770593993 2419437131847701077945495)
            ·
              refine ⟨3629155697771551616918243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419437131847701077945495 3629155697771551616918243)
              ·
                refine ⟨5443733546657327425377365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3629155697771551616918243 5443733546657327425377365)
                ·
                  refine ⟨63793752499890555766141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5443733546657327425377365 63793752499890555766141)
                  ·
                    rfl

theorem cell23_1118141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_1118141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118141 prefixEnd_1118141 := by exact prefixLift 1118141
  have htrace : WordTrace (prefixWord ++ tailWord_1118141) baseStart_1118141 baseEnd_1118141 := by
    simpa [prefixWord, tailWord_1118141, baseEnd_1118141] using wordTrace_append hprefix tailTrace_1118141
  have hstable : (prefixWord ++ tailWord_1118141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118141).length < 2 ^ (prefixWord ++ tailWord_1118141).sum := by decide
  have hdescent : baseEnd_1118141 < baseStart_1118141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118144 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_1118144 : Nat := 118140960795 + 1118144 * 2 ^ 59
def prefixEnd_1118144 : Nat := 4983230072969 + 3 ^ 40 * 1118144 * 2
def baseEnd_1118144 : Nat := 574145312940978490157755

theorem tailTrace_1118144 : CollatzResearch.WordTrace tailWord_1118144 prefixEnd_1118144 574145312940978490157755 := by
  unfold tailWord_1118144
  simp only [CollatzResearch.WordTrace]
  refine ⟨20391031030581363318452743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27188041374108484424603657 20391031030581363318452743)
  ·
    refine ⟨30586546545872044977679115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20391031030581363318452743 30586546545872044977679115)
    ·
      refine ⟨45879819818808067466518673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30586546545872044977679115 45879819818808067466518673)
      ·
        refine ⟨34409864864106050599889005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45879819818808067466518673 34409864864106050599889005)
        ·
          refine ⟨12903699324039768974958377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34409864864106050599889005 12903699324039768974958377)
          ·
            refine ⟨9677774493029826731218783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12903699324039768974958377 9677774493029826731218783)
            ·
              refine ⟨14516661739544740096828175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9677774493029826731218783 14516661739544740096828175)
              ·
                refine ⟨21774992609317110145242263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14516661739544740096828175 21774992609317110145242263)
                ·
                  refine ⟨32662488913975665217863395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21774992609317110145242263 32662488913975665217863395)
                  ·
                    refine ⟨48993733370963497826795093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32662488913975665217863395 48993733370963497826795093)
                    ·
                      refine ⟨574145312940978490157755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 48993733370963497826795093 574145312940978490157755)
                      ·
                        rfl

theorem cell23_1118144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_1118144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118144 prefixEnd_1118144 := by exact prefixLift 1118144
  have htrace : WordTrace (prefixWord ++ tailWord_1118144) baseStart_1118144 baseEnd_1118144 := by
    simpa [prefixWord, tailWord_1118144, baseEnd_1118144] using wordTrace_append hprefix tailTrace_1118144
  have hstable : (prefixWord ++ tailWord_1118144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118144).length < 2 ^ (prefixWord ++ tailWord_1118144).sum := by decide
  have hdescent : baseEnd_1118144 < baseStart_1118144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118158 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_1118158 : Nat := 118140960795 + 1118158 * 2 ^ 59
def prefixEnd_1118158 : Nat := 4983230072969 + 3 ^ 40 * 1118158 * 2
def baseEnd_1118158 : Nat := 63794722407793492820299

theorem tailTrace_1118158 : CollatzResearch.WordTrace tailWord_1118158 prefixEnd_1118158 63794722407793492820299 := by
  unfold tailWord_1118158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097821585389000878489391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27188381788741338018610085 5097821585389000878489391)
  ·
    refine ⟨7646732378083501317734087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5097821585389000878489391 7646732378083501317734087)
    ·
      refine ⟨11470098567125251976601131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7646732378083501317734087 11470098567125251976601131)
      ·
        refine ⟨17205147850687877964901697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11470098567125251976601131 17205147850687877964901697)
        ·
          refine ⟨12903860888015908473676273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17205147850687877964901697 12903860888015908473676273)
          ·
            refine ⟨9677895666011931355257205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12903860888015908473676273 9677895666011931355257205)
            ·
              refine ⟨907302718688618564555363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9677895666011931355257205 907302718688618564555363)
              ·
                refine ⟨1360954078032927846833045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907302718688618564555363 1360954078032927846833045)
                ·
                  refine ⟨63794722407793492820299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1360954078032927846833045 63794722407793492820299)
                  ·
                    rfl

theorem cell23_1118158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_1118158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118158 prefixEnd_1118158 := by exact prefixLift 1118158
  have htrace : WordTrace (prefixWord ++ tailWord_1118158) baseStart_1118158 baseEnd_1118158 := by
    simpa [prefixWord, tailWord_1118158, baseEnd_1118158] using wordTrace_append hprefix tailTrace_1118158
  have hstable : (prefixWord ++ tailWord_1118158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118158).length < 2 ^ (prefixWord ++ tailWord_1118158).sum := by decide
  have hdescent : baseEnd_1118158 < baseStart_1118158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118168 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_1118168 : Nat := 118140960795 + 1118168 * 2 ^ 59
def prefixEnd_1118168 : Nat := 4983230072969 + 3 ^ 40 * 1118168 * 2
def baseEnd_1118168 : Nat := 574157636476686396257645

theorem tailTrace_1118168 : CollatzResearch.WordTrace tailWord_1118168 prefixEnd_1118168 574157636476686396257645 := by
  unfold tailWord_1118168
  simp only [CollatzResearch.WordTrace]
  refine ⟨20391468706537889367889579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27188624942050519157186105 20391468706537889367889579)
  ·
    refine ⟨30587203059806834051834369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20391468706537889367889579 30587203059806834051834369)
    ·
      refine ⟨22940402294855125538875777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30587203059806834051834369 22940402294855125538875777)
      ·
        refine ⟨17205301721141344154156833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22940402294855125538875777 17205301721141344154156833)
        ·
          refine ⟨12903976290856008115617625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17205301721141344154156833 12903976290856008115617625)
          ·
            refine ⟨9677982218142006086713219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12903976290856008115617625 9677982218142006086713219)
            ·
              refine ⟨14516973327213009130069829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9677982218142006086713219 14516973327213009130069829)
              ·
                refine ⟨2721932498852439211888093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14516973327213009130069829 2721932498852439211888093)
                ·
                  refine ⟨1020724687069664704458035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2721932498852439211888093 1020724687069664704458035)
                  ·
                    refine ⟨1531087030604497056687053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1020724687069664704458035 1531087030604497056687053)
                    ·
                      refine ⟨574157636476686396257645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1531087030604497056687053 574157636476686396257645)
                      ·
                        rfl

theorem cell23_1118168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_1118168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118168 prefixEnd_1118168 := by exact prefixLift 1118168
  have htrace : WordTrace (prefixWord ++ tailWord_1118168) baseStart_1118168 baseEnd_1118168 := by
    simpa [prefixWord, tailWord_1118168, baseEnd_1118168] using wordTrace_append hprefix tailTrace_1118168
  have hstable : (prefixWord ++ tailWord_1118168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118168).length < 2 ^ (prefixWord ++ tailWord_1118168).sum := by decide
  have hdescent : baseEnd_1118168 < baseStart_1118168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118248 : List Nat := [2, 1, 5, 3, 1, 11]
def baseStart_1118248 : Nat := 118140960795 + 1118248 * 2 ^ 59
def prefixEnd_1118248 : Nat := 4983230072969 + 3 ^ 40 * 1118248 * 2
def baseEnd_1118248 : Nat := 2362957674605127914639

theorem tailTrace_1118248 : CollatzResearch.WordTrace tailWord_1118248 prefixEnd_1118248 2362957674605127914639 := by
  unfold tailWord_1118248
  simp only [CollatzResearch.WordTrace]
  refine ⟨20392927626392976199345699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27190570168523968265794265 20392927626392976199345699)
  ·
    refine ⟨30589391439589464299018549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20392927626392976199345699 30589391439589464299018549)
    ·
      refine ⟨2867755447461512278032989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30589391439589464299018549 2867755447461512278032989)
      ·
        refine ⟨1075408292798067104262371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2867755447461512278032989 1075408292798067104262371)
        ·
          refine ⟨1613112439197100656393557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075408292798067104262371 1613112439197100656393557)
          ·
            refine ⟨2362957674605127914639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1613112439197100656393557 2362957674605127914639)
            ·
              rfl

theorem cell23_1118248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 11].length) (baseStart_1118248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118248 prefixEnd_1118248 := by exact prefixLift 1118248
  have htrace : WordTrace (prefixWord ++ tailWord_1118248) baseStart_1118248 baseEnd_1118248 := by
    simpa [prefixWord, tailWord_1118248, baseEnd_1118248] using wordTrace_append hprefix tailTrace_1118248
  have hstable : (prefixWord ++ tailWord_1118248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118248).length < 2 ^ (prefixWord ++ tailWord_1118248).sum := by decide
  have hdescent : baseEnd_1118248 < baseStart_1118248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118259 : List Nat := [1, 1, 1, 2, 4, 1, 6, 2, 1, 2, 2]
def baseStart_1118259 : Nat := 118140960795 + 1118259 * 2 ^ 59
def prefixEnd_1118259 : Nat := 4983230072969 + 3 ^ 40 * 1118259 * 2
def baseEnd_1118259 : Nat := 574204363216245540219727

theorem tailTrace_1118259 : CollatzResearch.WordTrace tailWord_1118259 prefixEnd_1118259 574204363216245540219727 := by
  unfold tailWord_1118259
  simp only [CollatzResearch.WordTrace]
  refine ⟨40786256455746101277341831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27190837637164067518227887 40786256455746101277341831)
  ·
    refine ⟨61179384683619151916012747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40786256455746101277341831 61179384683619151916012747)
    ·
      refine ⟨91769077025428727874019121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61179384683619151916012747 91769077025428727874019121)
      ·
        refine ⟨68826807769071545905514341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91769077025428727874019121 68826807769071545905514341)
        ·
          refine ⟨12905026456700914857283939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68826807769071545905514341 12905026456700914857283939)
          ·
            refine ⟨19357539685051372285925909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12905026456700914857283939 19357539685051372285925909)
            ·
              refine ⟨907384672736783075902777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19357539685051372285925909 907384672736783075902777)
              ·
                refine ⟨680538504552587306927083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907384672736783075902777 680538504552587306927083)
                ·
                  refine ⟨1020807756828880960390625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680538504552587306927083 1020807756828880960390625)
                  ·
                    refine ⟨765605817621660720292969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1020807756828880960390625 765605817621660720292969)
                    ·
                      refine ⟨574204363216245540219727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765605817621660720292969 574204363216245540219727)
                      ·
                        rfl

theorem cell23_1118259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 2, 2].length) (baseStart_1118259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118259 prefixEnd_1118259 := by exact prefixLift 1118259
  have htrace : WordTrace (prefixWord ++ tailWord_1118259) baseStart_1118259 baseEnd_1118259 := by
    simpa [prefixWord, tailWord_1118259, baseEnd_1118259] using wordTrace_append hprefix tailTrace_1118259
  have hstable : (prefixWord ++ tailWord_1118259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118259).length < 2 ^ (prefixWord ++ tailWord_1118259).sum := by decide
  have hdescent : baseEnd_1118259 < baseStart_1118259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118261 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1118261 : Nat := 118140960795 + 1118261 * 2 ^ 59
def prefixEnd_1118261 : Nat := 4983230072969 + 3 ^ 40 * 1118261 * 2
def baseEnd_1118261 : Nat := 191401796725851510798239

theorem tailTrace_1118261 : CollatzResearch.WordTrace tailWord_1118261 prefixEnd_1118261 191401796725851510798239 := by
  unfold tailWord_1118261
  simp only [CollatzResearch.WordTrace]
  refine ⟨40786329401738855618914637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27190886267825903745943091 40786329401738855618914637)
  ·
    refine ⟨15294873525652070857092989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40786329401738855618914637 15294873525652070857092989)
    ·
      refine ⟨5735577572119526571409871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15294873525652070857092989 5735577572119526571409871)
      ·
        refine ⟨8603366358179289857114807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5735577572119526571409871 8603366358179289857114807)
        ·
          refine ⟨12905049537268934785672211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8603366358179289857114807 12905049537268934785672211)
          ·
            refine ⟨19357574305903402178508317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12905049537268934785672211 19357574305903402178508317)
            ·
              refine ⟨7259090364713775816940619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19357574305903402178508317 7259090364713775816940619)
              ·
                refine ⟨10888635547070663725410929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7259090364713775816940619 10888635547070663725410929)
                ·
                  refine ⟨8166476660302997794058197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10888635547070663725410929 8166476660302997794058197)
                  ·
                    refine ⟨191401796725851510798239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8166476660302997794058197 191401796725851510798239)
                    ·
                      rfl

theorem cell23_1118261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1118261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118261 prefixEnd_1118261 := by exact prefixLift 1118261
  have htrace : WordTrace (prefixWord ++ tailWord_1118261) baseStart_1118261 baseEnd_1118261 := by
    simpa [prefixWord, tailWord_1118261, baseEnd_1118261] using wordTrace_append hprefix tailTrace_1118261
  have hstable : (prefixWord ++ tailWord_1118261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118261).length < 2 ^ (prefixWord ++ tailWord_1118261).sum := by decide
  have hdescent : baseEnd_1118261 < baseStart_1118261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118265 : List Nat := [1, 2, 1, 5, 4, 1, 1, 8]
def baseStart_1118265 : Nat := 118140960795 + 1118265 * 2 ^ 59
def prefixEnd_1118265 : Nat := 4983230072969 + 3 ^ 40 * 1118265 * 2
def baseEnd_1118265 : Nat := 21266942374080463583137

theorem tailTrace_1118265 : CollatzResearch.WordTrace tailWord_1118265 prefixEnd_1118265 21266942374080463583137 := by
  unfold tailWord_1118265
  simp only [CollatzResearch.WordTrace]
  refine ⟨40786475293724364302060249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27190983529149576201373499 40786475293724364302060249)
  ·
    refine ⟨30589856470293273226545187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40786475293724364302060249 30589856470293273226545187)
    ·
      refine ⟨45884784705439909839817781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30589856470293273226545187 45884784705439909839817781)
      ·
        refine ⟨4301698566134991547482917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45884784705439909839817781 4301698566134991547482917)
        ·
          refine ⟨806568481150310915153047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4301698566134991547482917 806568481150310915153047)
          ·
            refine ⟨1209852721725466372729571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806568481150310915153047 1209852721725466372729571)
            ·
              refine ⟨1814779082588199559094357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209852721725466372729571 1814779082588199559094357)
              ·
                refine ⟨21266942374080463583137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1814779082588199559094357 21266942374080463583137)
                ·
                  rfl

theorem cell23_1118265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 8].length) (baseStart_1118265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118265 prefixEnd_1118265 := by exact prefixLift 1118265
  have htrace : WordTrace (prefixWord ++ tailWord_1118265) baseStart_1118265 baseEnd_1118265 := by
    simpa [prefixWord, tailWord_1118265, baseEnd_1118265] using wordTrace_append hprefix tailTrace_1118265
  have hstable : (prefixWord ++ tailWord_1118265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118265).length < 2 ^ (prefixWord ++ tailWord_1118265).sum := by decide
  have hdescent : baseEnd_1118265 < baseStart_1118265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118281 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_1118281 : Nat := 118140960795 + 1118281 * 2 ^ 59
def prefixEnd_1118281 : Nat := 4983230072969 + 3 ^ 40 * 1118281 * 2
def baseEnd_1118281 : Nat := 574215659790644454144625

theorem tailTrace_1118281 : CollatzResearch.WordTrace tailWord_1118281 prefixEnd_1118281 574215659790644454144625 := by
  unfold tailWord_1118281
  simp only [CollatzResearch.WordTrace]
  refine ⟨40787058861666399034642697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27191372574444266023095131 40787058861666399034642697)
  ·
    refine ⟨30590294146249799275982023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40787058861666399034642697 30590294146249799275982023)
    ·
      refine ⟨45885441219374698913973035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30590294146249799275982023 45885441219374698913973035)
      ·
        refine ⟨68828161829062048370959553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45885441219374698913973035 68828161829062048370959553)
        ·
          refine ⟨51621121371796536278219665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68828161829062048370959553 51621121371796536278219665)
          ·
            refine ⟨38715841028847402208664749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51621121371796536278219665 38715841028847402208664749)
            ·
              refine ⟨14518440385817775828249281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38715841028847402208664749 14518440385817775828249281)
              ·
                refine ⟨10888830289363331871186961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14518440385817775828249281 10888830289363331871186961)
                ·
                  refine ⟨8166622717022498903390221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10888830289363331871186961 8166622717022498903390221)
                  ·
                    refine ⟨3062483518883437088771333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8166622717022498903390221 3062483518883437088771333)
                    ·
                      refine ⟨574215659790644454144625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3062483518883437088771333 574215659790644454144625)
                      ·
                        rfl

theorem cell23_1118281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_1118281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118281 prefixEnd_1118281 := by exact prefixLift 1118281
  have htrace : WordTrace (prefixWord ++ tailWord_1118281) baseStart_1118281 baseEnd_1118281 := by
    simpa [prefixWord, tailWord_1118281, baseEnd_1118281] using wordTrace_append hprefix tailTrace_1118281
  have hstable : (prefixWord ++ tailWord_1118281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118281).length < 2 ^ (prefixWord ++ tailWord_1118281).sum := by decide
  have hdescent : baseEnd_1118281 < baseStart_1118281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118332 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_1118332 : Nat := 118140960795 + 1118332 * 2 ^ 59
def prefixEnd_1118332 : Nat := 4983230072969 + 3 ^ 40 * 1118332 * 2
def baseEnd_1118332 : Nat := 574241847304023754606891

theorem tailTrace_1118332 : CollatzResearch.WordTrace tailWord_1118332 prefixEnd_1118332 574241847304023754606891 := by
  unfold tailWord_1118332
  simp only [CollatzResearch.WordTrace]
  refine ⟨20394459492240817372374625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27192612656321089829832833 20394459492240817372374625)
  ·
    refine ⟨15295844619180613029280969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20394459492240817372374625 15295844619180613029280969)
    ·
      refine ⟨11471883464385459771960727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15295844619180613029280969 11471883464385459771960727)
      ·
        refine ⟨17207825196578189657941091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11471883464385459771960727 17207825196578189657941091)
        ·
          refine ⟨25811737794867284486911637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17207825196578189657941091 25811737794867284486911637)
          ·
            refine ⟨1209925209134403960323983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25811737794867284486911637 1209925209134403960323983)
            ·
              refine ⟨1814887813701605940485975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209925209134403960323983 1814887813701605940485975)
              ·
                refine ⟨2722331720552408910728963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814887813701605940485975 2722331720552408910728963)
                ·
                  refine ⟨4083497580828613366093445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722331720552408910728963 4083497580828613366093445)
                  ·
                    refine ⟨765655796405365006142521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083497580828613366093445 765655796405365006142521)
                    ·
                      refine ⟨574241847304023754606891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765655796405365006142521 574241847304023754606891)
                      ·
                        rfl

theorem cell23_1118332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_1118332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118332 prefixEnd_1118332 := by exact prefixLift 1118332
  have htrace : WordTrace (prefixWord ++ tailWord_1118332) baseStart_1118332 baseEnd_1118332 := by
    simpa [prefixWord, tailWord_1118332, baseEnd_1118332] using wordTrace_append hprefix tailTrace_1118332
  have hstable : (prefixWord ++ tailWord_1118332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118332).length < 2 ^ (prefixWord ++ tailWord_1118332).sum := by decide
  have hdescent : baseEnd_1118332 < baseStart_1118332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118361 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_1118361 : Nat := 118140960795 + 1118361 * 2 ^ 59
def prefixEnd_1118361 : Nat := 4983230072969 + 3 ^ 40 * 1118361 * 2
def baseEnd_1118361 : Nat := 574256738243004141144257

theorem tailTrace_1118361 : CollatzResearch.WordTrace tailWord_1118361 prefixEnd_1118361 574256738243004141144257 := by
  unfold tailWord_1118361
  simp only [CollatzResearch.WordTrace]
  refine ⟨40789976701376572697554937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27193317800917715131703291 40789976701376572697554937)
  ·
    refine ⟨30592482526032429523166203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40789976701376572697554937 30592482526032429523166203)
    ·
      refine ⟨45888723789048644284749305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30592482526032429523166203 45888723789048644284749305)
      ·
        refine ⟨34416542841786483213561979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45888723789048644284749305 34416542841786483213561979)
        ·
          refine ⟨51624814262679724820342969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34416542841786483213561979 51624814262679724820342969)
          ·
            refine ⟨38718610697009793615257227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51624814262679724820342969 38718610697009793615257227)
            ·
              refine ⟨58077916045514690422885841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38718610697009793615257227 58077916045514690422885841)
              ·
                refine ⟨43558437034136017817164381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58077916045514690422885841 43558437034136017817164381)
                ·
                  refine ⟨16334413887801006681436643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43558437034136017817164381 16334413887801006681436643)
                  ·
                    refine ⟨24501620831701510022154965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16334413887801006681436643 24501620831701510022154965)
                    ·
                      refine ⟨574256738243004141144257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24501620831701510022154965 574256738243004141144257)
                      ·
                        rfl

theorem cell23_1118361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_1118361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118361 prefixEnd_1118361 := by exact prefixLift 1118361
  have htrace : WordTrace (prefixWord ++ tailWord_1118361) baseStart_1118361 baseEnd_1118361 := by
    simpa [prefixWord, tailWord_1118361, baseEnd_1118361] using wordTrace_append hprefix tailTrace_1118361
  have hstable : (prefixWord ++ tailWord_1118361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118361).length < 2 ^ (prefixWord ++ tailWord_1118361).sum := by decide
  have hdescent : baseEnd_1118361 < baseStart_1118361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118368 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 4, 5]
def baseStart_1118368 : Nat := 118140960795 + 1118368 * 2 ^ 59
def prefixEnd_1118368 : Nat := 4983230072969 + 3 ^ 40 * 1118368 * 2
def baseEnd_1118368 : Nat := 191420110869195204585575

theorem tailTrace_1118368 : CollatzResearch.WordTrace tailWord_1118368 prefixEnd_1118368 191420110869195204585575 := by
  unfold tailWord_1118368
  simp only [CollatzResearch.WordTrace]
  refine ⟨20395116006175606446529879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27193488008234141928706505 20395116006175606446529879)
  ·
    refine ⟨30592674009263409669794819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20395116006175606446529879 30592674009263409669794819)
    ·
      refine ⟨45889011013895114504692229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30592674009263409669794819 45889011013895114504692229)
      ·
        refine ⟨8604189565105333969629793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45889011013895114504692229 8604189565105333969629793)
        ·
          refine ⟨6453142173829000477222345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8604189565105333969629793 6453142173829000477222345)
          ·
            refine ⟨4839856630371750357916759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6453142173829000477222345 4839856630371750357916759)
            ·
              refine ⟨7259784945557625536875139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839856630371750357916759 7259784945557625536875139)
              ·
                refine ⟨10889677418336438305312709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7259784945557625536875139 10889677418336438305312709)
                ·
                  refine ⟨2041814515938082182246133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10889677418336438305312709 2041814515938082182246133)
                  ·
                    refine ⟨191420110869195204585575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2041814515938082182246133 191420110869195204585575)
                    ·
                      rfl

theorem cell23_1118368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_1118368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118368 prefixEnd_1118368 := by exact prefixLift 1118368
  have htrace : WordTrace (prefixWord ++ tailWord_1118368) baseStart_1118368 baseEnd_1118368 := by
    simpa [prefixWord, tailWord_1118368, baseEnd_1118368] using wordTrace_append hprefix tailTrace_1118368
  have hstable : (prefixWord ++ tailWord_1118368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118368).length < 2 ^ (prefixWord ++ tailWord_1118368).sum := by decide
  have hdescent : baseEnd_1118368 < baseStart_1118368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118371 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1118371 : Nat := 118140960795 + 1118371 * 2 ^ 59
def prefixEnd_1118371 : Nat := 4983230072969 + 3 ^ 40 * 1118371 * 2
def baseEnd_1118371 : Nat := 574261873049549102019211

theorem tailTrace_1118371 : CollatzResearch.WordTrace tailWord_1118371 prefixEnd_1118371 574261873049549102019211 := by
  unfold tailWord_1118371
  simp only [CollatzResearch.WordTrace]
  refine ⟨40790341431340344405418967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27193560954226896270279311 40790341431340344405418967)
  ·
    refine ⟨61185512147010516608128451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40790341431340344405418967 61185512147010516608128451)
    ·
      refine ⟨91778268220515774912192677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61185512147010516608128451 91778268220515774912192677)
      ·
        refine ⟨17208425291346707796036127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91778268220515774912192677 17208425291346707796036127)
        ·
          refine ⟨25812637937020061694054191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17208425291346707796036127 25812637937020061694054191)
          ·
            refine ⟨38718956905530092541081287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25812637937020061694054191 38718956905530092541081287)
            ·
              refine ⟨58078435358295138811621931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38718956905530092541081287 58078435358295138811621931)
              ·
                refine ⟨87117653037442708217432897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58078435358295138811621931 87117653037442708217432897)
                ·
                  refine ⟨65338239778082031163074673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87117653037442708217432897 65338239778082031163074673)
                  ·
                    refine ⟨49003679833561523372306005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65338239778082031163074673 49003679833561523372306005)
                    ·
                      refine ⟨574261873049549102019211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 49003679833561523372306005 574261873049549102019211)
                      ·
                        rfl

theorem cell23_1118371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1118371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118371 prefixEnd_1118371 := by exact prefixLift 1118371
  have htrace : WordTrace (prefixWord ++ tailWord_1118371) baseStart_1118371 baseEnd_1118371 := by
    simpa [prefixWord, tailWord_1118371, baseEnd_1118371] using wordTrace_append hprefix tailTrace_1118371
  have hstable : (prefixWord ++ tailWord_1118371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118371).length < 2 ^ (prefixWord ++ tailWord_1118371).sum := by decide
  have hdescent : baseEnd_1118371 < baseStart_1118371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118372 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 7]
def baseStart_1118372 : Nat := 118140960795 + 1118372 * 2 ^ 59
def prefixEnd_1118372 : Nat := 4983230072969 + 3 ^ 40 * 1118372 * 2
def baseEnd_1118372 : Nat := 63806931836689288678523

theorem tailTrace_1118372 : CollatzResearch.WordTrace tailWord_1118372 prefixEnd_1118372 63806931836689288678523 := by
  unfold tailWord_1118372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20395188952168360788102685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27193585269557814384136913 20395188952168360788102685)
  ·
    refine ⟨7648195857063135295538507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20395188952168360788102685 7648195857063135295538507)
    ·
      refine ⟨11472293785594702943307761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7648195857063135295538507 11472293785594702943307761)
      ·
        refine ⟨8604220339196027207480821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11472293785594702943307761 8604220339196027207480821)
        ·
          refine ⟨806645656799627550701327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8604220339196027207480821 806645656799627550701327)
          ·
            refine ⟨1209968485199441326051991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806645656799627550701327 1209968485199441326051991)
            ·
              refine ⟨1814952727799161989077987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209968485199441326051991 1814952727799161989077987)
              ·
                refine ⟨2722429091698742983616981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814952727799161989077987 2722429091698742983616981)
                ·
                  refine ⟨63806931836689288678523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2722429091698742983616981 63806931836689288678523)
                  ·
                    rfl

theorem cell23_1118372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_1118372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118372 prefixEnd_1118372 := by exact prefixLift 1118372
  have htrace : WordTrace (prefixWord ++ tailWord_1118372) baseStart_1118372 baseEnd_1118372 := by
    simpa [prefixWord, tailWord_1118372, baseEnd_1118372] using wordTrace_append hprefix tailTrace_1118372
  have hstable : (prefixWord ++ tailWord_1118372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118372).length < 2 ^ (prefixWord ++ tailWord_1118372).sum := by decide
  have hdescent : baseEnd_1118372 < baseStart_1118372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118425 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 3]
def baseStart_1118425 : Nat := 118140960795 + 1118425 * 2 ^ 59
def prefixEnd_1118425 : Nat := 4983230072969 + 3 ^ 40 * 1118425 * 2
def baseEnd_1118425 : Nat := 574289601004891890743963

theorem tailTrace_1118425 : CollatzResearch.WordTrace tailWord_1118425 prefixEnd_1118425 574289601004891890743963 := by
  unfold tailWord_1118425
  simp only [CollatzResearch.WordTrace]
  refine ⟨40792310973144711627884729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27194873982096474418589819 40792310973144711627884729)
  ·
    refine ⟨30594233229858533720913547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40792310973144711627884729 30594233229858533720913547)
    ·
      refine ⟨45891349844787800581370321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30594233229858533720913547 45891349844787800581370321)
      ·
        refine ⟨34418512383590850436027741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45891349844787800581370321 34418512383590850436027741)
        ·
          refine ⟨12906942143846568913510403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34418512383590850436027741 12906942143846568913510403)
          ·
            refine ⟨19360413215769853370265605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12906942143846568913510403 19360413215769853370265605)
            ·
              refine ⟨3630077477956847506924801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19360413215769853370265605 3630077477956847506924801)
              ·
                refine ⟨2722558108467635630193601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630077477956847506924801 2722558108467635630193601)
                ·
                  refine ⟨2041918581350726722645201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2722558108467635630193601 2041918581350726722645201)
                  ·
                    refine ⟨1531438936013045041983901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2041918581350726722645201 1531438936013045041983901)
                    ·
                      refine ⟨574289601004891890743963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1531438936013045041983901 574289601004891890743963)
                      ·
                        rfl

theorem cell23_1118425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_1118425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118425 prefixEnd_1118425 := by exact prefixLift 1118425
  have htrace : WordTrace (prefixWord ++ tailWord_1118425) baseStart_1118425 baseEnd_1118425 := by
    simpa [prefixWord, tailWord_1118425, baseEnd_1118425] using wordTrace_append hprefix tailTrace_1118425
  have hstable : (prefixWord ++ tailWord_1118425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118425).length < 2 ^ (prefixWord ++ tailWord_1118425).sum := by decide
  have hdescent : baseEnd_1118425 < baseStart_1118425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118432 : List Nat := [2, 1, 1, 3, 1, 3, 3, 4, 1, 4]
def baseStart_1118432 : Nat := 118140960795 + 1118432 * 2 ^ 59
def prefixEnd_1118432 : Nat := 4983230072969 + 3 ^ 40 * 1118432 * 2
def baseEnd_1118432 : Nat := 191431065123157787785477

theorem tailTrace_1118432 : CollatzResearch.WordTrace tailWord_1118432 prefixEnd_1118432 191431065123157787785477 := by
  unfold tailWord_1118432
  simp only [CollatzResearch.WordTrace]
  refine ⟨20396283142059675911694775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27195044189412901215593033 20396283142059675911694775)
  ·
    refine ⟨30594424713089513867542163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20396283142059675911694775 30594424713089513867542163)
    ·
      refine ⟨45891637069634270801313245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30594424713089513867542163 45891637069634270801313245)
      ·
        refine ⟨17209363901112851550492467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45891637069634270801313245 17209363901112851550492467)
        ·
          refine ⟨25814045851669277325738701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17209363901112851550492467 25814045851669277325738701)
          ·
            refine ⟨9680267194375978997152013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25814045851669277325738701 9680267194375978997152013)
            ·
              refine ⟨3630100197890992123932005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9680267194375978997152013 3630100197890992123932005)
              ·
                refine ⟨680643787104561023237251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3630100197890992123932005 680643787104561023237251)
                ·
                  refine ⟨1020965680656841534855877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680643787104561023237251 1020965680656841534855877)
                  ·
                    refine ⟨191431065123157787785477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1020965680656841534855877 191431065123157787785477)
                    ·
                      rfl

theorem cell23_1118432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 4].length) (baseStart_1118432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118432 prefixEnd_1118432 := by exact prefixLift 1118432
  have htrace : WordTrace (prefixWord ++ tailWord_1118432) baseStart_1118432 baseEnd_1118432 := by
    simpa [prefixWord, tailWord_1118432, baseEnd_1118432] using wordTrace_append hprefix tailTrace_1118432
  have hstable : (prefixWord ++ tailWord_1118432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118432).length < 2 ^ (prefixWord ++ tailWord_1118432).sum := by decide
  have hdescent : baseEnd_1118432 < baseStart_1118432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118466 : List Nat := [3, 4, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1118466 : Nat := 118140960795 + 1118466 * 2 ^ 59
def prefixEnd_1118466 : Nat := 4983230072969 + 3 ^ 40 * 1118466 * 2
def baseEnd_1118466 : Nat := 191436884570575410110425

theorem tailTrace_1118466 : CollatzResearch.WordTrace tailWord_1118466 prefixEnd_1118466 191436884570575410110425 := by
  unfold tailWord_1118466
  simp only [CollatzResearch.WordTrace]
  refine ⟨10198451591499043907531813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27195870910664117086751501 10198451591499043907531813)
  ·
    refine ⟨1912209673406070732662215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10198451591499043907531813 1912209673406070732662215)
    ·
      refine ⟨2868314510109106098993323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912209673406070732662215 2868314510109106098993323)
      ·
        refine ⟨4302471765163659148489985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868314510109106098993323 4302471765163659148489985)
        ·
          refine ⟨3226853823872744361367489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4302471765163659148489985 3226853823872744361367489)
          ·
            refine ⟨2420140367904558271025617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3226853823872744361367489 2420140367904558271025617)
            ·
              refine ⟨1815105275928418703269213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420140367904558271025617 1815105275928418703269213)
              ·
                refine ⟨680664478473157013725955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1815105275928418703269213 680664478473157013725955)
                ·
                  refine ⟨1020996717709735520588933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680664478473157013725955 1020996717709735520588933)
                  ·
                    refine ⟨191436884570575410110425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1020996717709735520588933 191436884570575410110425)
                    ·
                      rfl

theorem cell23_1118466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1118466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118466 prefixEnd_1118466 := by exact prefixLift 1118466
  have htrace : WordTrace (prefixWord ++ tailWord_1118466) baseStart_1118466 baseEnd_1118466 := by
    simpa [prefixWord, tailWord_1118466, baseEnd_1118466] using wordTrace_append hprefix tailTrace_1118466
  have hstable : (prefixWord ++ tailWord_1118466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118466).length < 2 ^ (prefixWord ++ tailWord_1118466).sum := by decide
  have hdescent : baseEnd_1118466 < baseStart_1118466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118475 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 1, 5]
def baseStart_1118475 : Nat := 118140960795 + 1118475 * 2 ^ 59
def prefixEnd_1118475 : Nat := 4983230072969 + 3 ^ 40 * 1118475 * 2
def baseEnd_1118475 : Nat := 191438425012538898372911

theorem tailTrace_1118475 : CollatzResearch.WordTrace tailWord_1118475 prefixEnd_1118475 191438425012538898372911 := by
  unfold tailWord_1118475
  simp only [CollatzResearch.WordTrace]
  refine ⟨40794134622963570167204879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27196089748642380111469919 40794134622963570167204879)
  ·
    refine ⟨61191201934445355250807319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40794134622963570167204879 61191201934445355250807319)
    ·
      refine ⟨91786802901668032876210979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61191201934445355250807319 91786802901668032876210979)
      ·
        refine ⟨137680204352502049314316469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91786802901668032876210979 137680204352502049314316469)
        ·
          refine ⟨12907519158047067123217169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137680204352502049314316469 12907519158047067123217169)
          ·
            refine ⟨9680639368535300342412877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12907519158047067123217169 9680639368535300342412877)
            ·
              refine ⟨3630239763200737628404829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9680639368535300342412877 3630239763200737628404829)
              ·
                refine ⟨1361339911200276610651811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3630239763200737628404829 1361339911200276610651811)
                ·
                  refine ⟨2042009866800414915977717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361339911200276610651811 2042009866800414915977717)
                  ·
                    refine ⟨191438425012538898372911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2042009866800414915977717 191438425012538898372911)
                    ·
                      rfl

theorem cell23_1118475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 5].length) (baseStart_1118475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118475 prefixEnd_1118475 := by exact prefixLift 1118475
  have htrace : WordTrace (prefixWord ++ tailWord_1118475) baseStart_1118475 baseEnd_1118475 := by
    simpa [prefixWord, tailWord_1118475, baseEnd_1118475] using wordTrace_append hprefix tailTrace_1118475
  have hstable : (prefixWord ++ tailWord_1118475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118475).length < 2 ^ (prefixWord ++ tailWord_1118475).sum := by decide
  have hdescent : baseEnd_1118475 < baseStart_1118475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118512 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 5, 2, 2]
def baseStart_1118512 : Nat := 118140960795 + 1118512 * 2 ^ 59
def prefixEnd_1118512 : Nat := 4983230072969 + 3 ^ 40 * 1118512 * 2
def baseEnd_1118512 : Nat := 574334273821833050356063

theorem tailTrace_1118512 : CollatzResearch.WordTrace tailWord_1118512 prefixEnd_1118512 574334273821833050356063 := by
  unfold tailWord_1118512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20397742061914762743150895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27196989415886350324201193 20397742061914762743150895)
  ·
    refine ⟨30596613092872144114726343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20397742061914762743150895 30596613092872144114726343)
    ·
      refine ⟨45894919639308216172089515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30596613092872144114726343 45894919639308216172089515)
      ·
        refine ⟨68842379458962324258134273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45894919639308216172089515 68842379458962324258134273)
        ·
          refine ⟨51631784594221743193600705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68842379458962324258134273 51631784594221743193600705)
          ·
            refine ⟨38723838445666307395200529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51631784594221743193600705 38723838445666307395200529)
            ·
              refine ⟨29042878834249730546400397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38723838445666307395200529 29042878834249730546400397)
              ·
                refine ⟨10891079562843648954900149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29042878834249730546400397 10891079562843648954900149)
                ·
                  refine ⟨1021038709016592089521889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10891079562843648954900149 1021038709016592089521889)
                  ·
                    refine ⟨765779031762444067141417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1021038709016592089521889 765779031762444067141417)
                    ·
                      refine ⟨574334273821833050356063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765779031762444067141417 574334273821833050356063)
                      ·
                        rfl

theorem cell23_1118512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 2, 2].length) (baseStart_1118512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118512 prefixEnd_1118512 := by exact prefixLift 1118512
  have htrace : WordTrace (prefixWord ++ tailWord_1118512) baseStart_1118512 baseEnd_1118512 := by
    simpa [prefixWord, tailWord_1118512, baseEnd_1118512] using wordTrace_append hprefix tailTrace_1118512
  have hstable : (prefixWord ++ tailWord_1118512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118512).length < 2 ^ (prefixWord ++ tailWord_1118512).sum := by decide
  have hdescent : baseEnd_1118512 < baseStart_1118512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118546 : List Nat := [3, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_1118546 : Nat := 118140960795 + 1118546 * 2 ^ 59
def prefixEnd_1118546 : Nat := 4983230072969 + 3 ^ 40 * 1118546 * 2
def baseEnd_1118546 : Nat := 574351732164085917330907

theorem tailTrace_1118546 : CollatzResearch.WordTrace tailWord_1118546 prefixEnd_1118546 574351732164085917330907 := by
  unfold tailWord_1118546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10199181051426587323259873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27197816137137566195359661 10199181051426587323259873)
  ·
    refine ⟨7649385788569940492444905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10199181051426587323259873 7649385788569940492444905)
    ·
      refine ⟨5737039341427455369333679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7649385788569940492444905 5737039341427455369333679)
      ·
        refine ⟨8605559012141183054000519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5737039341427455369333679 8605559012141183054000519)
        ·
          refine ⟨12908338518211774581000779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8605559012141183054000519 12908338518211774581000779)
          ·
            refine ⟨19362507777317661871501169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12908338518211774581000779 19362507777317661871501169)
            ·
              refine ⟨14521880832988246403625877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19362507777317661871501169 14521880832988246403625877)
              ·
                refine ⟨680713164046324050169963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14521880832988246403625877 680713164046324050169963)
                ·
                  refine ⟨1021069746069486075254945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680713164046324050169963 1021069746069486075254945)
                  ·
                    refine ⟨765802309552114556441209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1021069746069486075254945 765802309552114556441209)
                    ·
                      refine ⟨574351732164085917330907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765802309552114556441209 574351732164085917330907)
                      ·
                        rfl

theorem cell23_1118546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_1118546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118546 prefixEnd_1118546 := by exact prefixLift 1118546
  have htrace : WordTrace (prefixWord ++ tailWord_1118546) baseStart_1118546 baseEnd_1118546 := by
    simpa [prefixWord, tailWord_1118546, baseEnd_1118546] using wordTrace_append hprefix tailTrace_1118546
  have hstable : (prefixWord ++ tailWord_1118546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118546).length < 2 ^ (prefixWord ++ tailWord_1118546).sum := by decide
  have hdescent : baseEnd_1118546 < baseStart_1118546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118556 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1118556 : Nat := 118140960795 + 1118556 * 2 ^ 59
def prefixEnd_1118556 : Nat := 4983230072969 + 3 ^ 40 * 1118556 * 2
def baseEnd_1118556 : Nat := 191452288990210292735287

theorem tailTrace_1118556 : CollatzResearch.WordTrace tailWord_1118556 prefixEnd_1118556 191452288990210292735287 := by
  unfold tailWord_1118556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20398544467835060500451761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27198059290446747333935681 20398544467835060500451761)
  ·
    refine ⟨15298908350876295375338821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20398544467835060500451761 15298908350876295375338821)
    ·
      refine ⟨2868545315789305382876029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15298908350876295375338821 2868545315789305382876029)
      ·
        refine ⟨1075704493420989518578511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2868545315789305382876029 1075704493420989518578511)
        ·
          refine ⟨1613556740131484277867767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075704493420989518578511 1613556740131484277867767)
          ·
            refine ⟨2420335110197226416801651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613556740131484277867767 2420335110197226416801651)
            ·
              refine ⟨3630502665295839625202477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420335110197226416801651 3630502665295839625202477)
              ·
                refine ⟨1361438499485939859450929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3630502665295839625202477 1361438499485939859450929)
                ·
                  refine ⟨1021078874614454894588197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1361438499485939859450929 1021078874614454894588197)
                  ·
                    refine ⟨191452288990210292735287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021078874614454894588197 191452288990210292735287)
                    ·
                      rfl

theorem cell23_1118556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1118556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118556 prefixEnd_1118556 := by exact prefixLift 1118556
  have htrace : WordTrace (prefixWord ++ tailWord_1118556) baseStart_1118556 baseEnd_1118556 := by
    simpa [prefixWord, tailWord_1118556, baseEnd_1118556] using wordTrace_append hprefix tailTrace_1118556
  have hstable : (prefixWord ++ tailWord_1118556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118556).length < 2 ^ (prefixWord ++ tailWord_1118556).sum := by decide
  have hdescent : baseEnd_1118556 < baseStart_1118556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118615 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1118615 : Nat := 118140960795 + 1118615 * 2 ^ 59
def prefixEnd_1118615 : Nat := 4983230072969 + 3 ^ 40 * 1118615 * 2
def baseEnd_1118615 : Nat := 574387162329246147368089

theorem tailTrace_1118615 : CollatzResearch.WordTrace tailWord_1118615 prefixEnd_1118615 574387162329246147368089 := by
  unfold tailWord_1118615
  simp only [CollatzResearch.WordTrace]
  refine ⟨40799240842456374077301299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27199493894970916051534199 40799240842456374077301299)
  ·
    refine ⟨61198861263684561115951949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40799240842456374077301299 61198861263684561115951949)
    ·
      refine ⟨22949572973881710418481981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61198861263684561115951949 22949572973881710418481981)
      ·
        refine ⟨8606089865205641406930743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22949572973881710418481981 8606089865205641406930743)
        ·
          refine ⟨12909134797808462110396115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8606089865205641406930743 12909134797808462110396115)
          ·
            refine ⟨19363702196712693165594173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12909134797808462110396115 19363702196712693165594173)
            ·
              refine ⟨7261388323767259937097815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19363702196712693165594173 7261388323767259937097815)
              ·
                refine ⟨10892082485650889905646723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7261388323767259937097815 10892082485650889905646723)
                ·
                  refine ⟨16338123728476334858470085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10892082485650889905646723 16338123728476334858470085)
                  ·
                    refine ⟨3063398199089312785963141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16338123728476334858470085 3063398199089312785963141)
                    ·
                      refine ⟨574387162329246147368089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3063398199089312785963141 574387162329246147368089)
                      ·
                        rfl

theorem cell23_1118615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1118615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118615 prefixEnd_1118615 := by exact prefixLift 1118615
  have htrace : WordTrace (prefixWord ++ tailWord_1118615) baseStart_1118615 baseEnd_1118615 := by
    simpa [prefixWord, tailWord_1118615, baseEnd_1118615] using wordTrace_append hprefix tailTrace_1118615
  have hstable : (prefixWord ++ tailWord_1118615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118615).length < 2 ^ (prefixWord ++ tailWord_1118615).sum := by decide
  have hdescent : baseEnd_1118615 < baseStart_1118615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118653 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_1118653 : Nat := 118140960795 + 1118653 * 2 ^ 59
def prefixEnd_1118653 : Nat := 4983230072969 + 3 ^ 40 * 1118653 * 2
def baseEnd_1118653 : Nat := 574406674594116998692915

theorem tailTrace_1118653 : CollatzResearch.WordTrace tailWord_1118653 prefixEnd_1118653 574406674594116998692915 := by
  unfold tailWord_1118653
  simp only [CollatzResearch.WordTrace]
  refine ⟨40800626816318706567184613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27200417877545804378123075 40800626816318706567184613)
  ·
    refine ⟨7650117528059757481347115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40800626816318706567184613 7650117528059757481347115)
    ·
      refine ⟨11475176292089636222020673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650117528059757481347115 11475176292089636222020673)
      ·
        refine ⟨8606382219067227166515505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11475176292089636222020673 8606382219067227166515505)
        ·
          refine ⟨6454786664300420374886629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8606382219067227166515505 6454786664300420374886629)
          ·
            refine ⟨1210272499556328820291243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6454786664300420374886629 1210272499556328820291243)
            ·
              refine ⟨1815408749334493230436865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210272499556328820291243 1815408749334493230436865)
              ·
                refine ⟨1361556562000869922827649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815408749334493230436865 1361556562000869922827649)
                ·
                  refine ⟨1021167421500652442120737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1361556562000869922827649 1021167421500652442120737)
                  ·
                    refine ⟨765875566125489331590553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1021167421500652442120737 765875566125489331590553)
                    ·
                      refine ⟨574406674594116998692915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 765875566125489331590553 574406674594116998692915)
                      ·
                        rfl

theorem cell23_1118653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_1118653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118653 prefixEnd_1118653 := by exact prefixLift 1118653
  have htrace : WordTrace (prefixWord ++ tailWord_1118653) baseStart_1118653 baseEnd_1118653 := by
    simpa [prefixWord, tailWord_1118653, baseEnd_1118653] using wordTrace_append hprefix tailTrace_1118653
  have hstable : (prefixWord ++ tailWord_1118653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118653).length < 2 ^ (prefixWord ++ tailWord_1118653).sum := by decide
  have hdescent : baseEnd_1118653 < baseStart_1118653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118665 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_1118665 : Nat := 118140960795 + 1118665 * 2 ^ 59
def prefixEnd_1118665 : Nat := 4983230072969 + 3 ^ 40 * 1118665 * 2
def baseEnd_1118665 : Nat := 574412836361970951742859

theorem tailTrace_1118665 : CollatzResearch.WordTrace tailWord_1118665 prefixEnd_1118665 574412836361970951742859 := by
  unfold tailWord_1118665
  simp only [CollatzResearch.WordTrace]
  refine ⟨40801064492275232616621449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27200709661516821744414299 40801064492275232616621449)
  ·
    refine ⟨30600798369206424462466087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40801064492275232616621449 30600798369206424462466087)
    ·
      refine ⟨45901197553809636693699131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30600798369206424462466087 45901197553809636693699131)
      ·
        refine ⟨68851796330714455040548697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45901197553809636693699131 68851796330714455040548697)
        ·
          refine ⟨51638847248035841280411523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68851796330714455040548697 51638847248035841280411523)
          ·
            refine ⟨77458270872053761920617285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51638847248035841280411523 77458270872053761920617285)
            ·
              refine ⟨14523425788510080360115741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77458270872053761920617285 14523425788510080360115741)
              ·
                refine ⟨5446284670691280135043403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14523425788510080360115741 5446284670691280135043403)
                ·
                  refine ⟨8169427006036920202565105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446284670691280135043403 8169427006036920202565105)
                  ·
                    refine ⟨6127070254527690151923829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8169427006036920202565105 6127070254527690151923829)
                    ·
                      refine ⟨574412836361970951742859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6127070254527690151923829 574412836361970951742859)
                      ·
                        rfl

theorem cell23_1118665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_1118665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118665 prefixEnd_1118665 := by exact prefixLift 1118665
  have htrace : WordTrace (prefixWord ++ tailWord_1118665) baseStart_1118665 baseEnd_1118665 := by
    simpa [prefixWord, tailWord_1118665, baseEnd_1118665] using wordTrace_append hprefix tailTrace_1118665
  have hstable : (prefixWord ++ tailWord_1118665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118665).length < 2 ^ (prefixWord ++ tailWord_1118665).sum := by decide
  have hdescent : baseEnd_1118665 < baseStart_1118665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118693 : List Nat := [1, 3, 1, 5, 3, 1, 1, 3, 5]
def baseStart_1118693 : Nat := 118140960795 + 1118693 * 2 ^ 59
def prefixEnd_1118693 : Nat := 4983230072969 + 3 ^ 40 * 1118693 * 2
def baseEnd_1118693 : Nat := 63825245980032982465859

theorem tailTrace_1118693 : CollatzResearch.WordTrace tailWord_1118693 prefixEnd_1118693 63825245980032982465859 := by
  unfold tailWord_1118693
  simp only [CollatzResearch.WordTrace]
  refine ⟨40802085736173793398640733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27201390490782528932427155 40802085736173793398640733)
  ·
    refine ⟨15300782151065172524490275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40802085736173793398640733 15300782151065172524490275)
    ·
      refine ⟨22951173226597758786735413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15300782151065172524490275 22951173226597758786735413)
      ·
        refine ⟨2151672489993539886256445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22951173226597758786735413 2151672489993539886256445)
        ·
          refine ⟨806877183747577457346167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2151672489993539886256445 806877183747577457346167)
          ·
            refine ⟨1210315775621366186019251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806877183747577457346167 1210315775621366186019251)
            ·
              refine ⟨1815473663432049279028877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210315775621366186019251 1815473663432049279028877)
              ·
                refine ⟨680802623787018479635829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1815473663432049279028877 680802623787018479635829)
                ·
                  refine ⟨63825245980032982465859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 680802623787018479635829 63825245980032982465859)
                  ·
                    rfl

theorem cell23_1118693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_1118693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118693 prefixEnd_1118693 := by exact prefixLift 1118693
  have htrace : WordTrace (prefixWord ++ tailWord_1118693) baseStart_1118693 baseEnd_1118693 := by
    simpa [prefixWord, tailWord_1118693, baseEnd_1118693] using wordTrace_append hprefix tailTrace_1118693
  have hstable : (prefixWord ++ tailWord_1118693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118693).length < 2 ^ (prefixWord ++ tailWord_1118693).sum := by decide
  have hdescent : baseEnd_1118693 < baseStart_1118693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118735 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_1118735 : Nat := 118140960795 + 1118735 * 2 ^ 59
def prefixEnd_1118735 : Nat := 4983230072969 + 3 ^ 40 * 1118735 * 2
def baseEnd_1118735 : Nat := 574448780007785677867537

theorem tailTrace_1118735 : CollatzResearch.WordTrace tailWord_1118735 prefixEnd_1118735 574448780007785677867537 := by
  unfold tailWord_1118735
  simp only [CollatzResearch.WordTrace]
  refine ⟨40803617602021634571669659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27202411734681089714446439 40803617602021634571669659)
  ·
    refine ⟨61205426403032451857504489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40803617602021634571669659 61205426403032451857504489)
    ·
      refine ⟨45904069802274338893128367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61205426403032451857504489 45904069802274338893128367)
      ·
        refine ⟨68856104703411508339692551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45904069802274338893128367 68856104703411508339692551)
        ·
          refine ⟨103284157055117262509538827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68856104703411508339692551 103284157055117262509538827)
          ·
            refine ⟨154926235582675893764308241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103284157055117262509538827 154926235582675893764308241)
            ·
              refine ⟨116194676687006920323231181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154926235582675893764308241 116194676687006920323231181)
              ·
                refine ⟨43573003757627595121211693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116194676687006920323231181 43573003757627595121211693)
                ·
                  refine ⟨16339876409110348170454385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43573003757627595121211693 16339876409110348170454385)
                  ·
                    refine ⟨12254907306832761127840789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16339876409110348170454385 12254907306832761127840789)
                    ·
                      refine ⟨574448780007785677867537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12254907306832761127840789 574448780007785677867537)
                      ·
                        rfl

theorem cell23_1118735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_1118735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118735 prefixEnd_1118735 := by exact prefixLift 1118735
  have htrace : WordTrace (prefixWord ++ tailWord_1118735) baseStart_1118735 baseEnd_1118735 := by
    simpa [prefixWord, tailWord_1118735, baseEnd_1118735] using wordTrace_append hprefix tailTrace_1118735
  have hstable : (prefixWord ++ tailWord_1118735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118735).length < 2 ^ (prefixWord ++ tailWord_1118735).sum := by decide
  have hdescent : baseEnd_1118735 < baseStart_1118735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118745 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 2, 9]
def baseStart_1118745 : Nat := 118140960795 + 1118745 * 2 ^ 59
def prefixEnd_1118745 : Nat := 4983230072969 + 3 ^ 40 * 1118745 * 2
def baseEnd_1118745 : Nat := 191484638271443546247497

theorem tailTrace_1118745 : CollatzResearch.WordTrace tailWord_1118745 prefixEnd_1118745 191484638271443546247497 := by
  unfold tailWord_1118745
  simp only [CollatzResearch.WordTrace]
  refine ⟨40803982331985406279533689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27202654887990270853022459 40803982331985406279533689)
  ·
    refine ⟨30602986748989054709650267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40803982331985406279533689 30602986748989054709650267)
    ·
      refine ⟨45904480123483582064475401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30602986748989054709650267 45904480123483582064475401)
      ·
        refine ⟨34428360092612686548356551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45904480123483582064475401 34428360092612686548356551)
        ·
          refine ⟨51642540138919029822534827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34428360092612686548356551 51642540138919029822534827)
          ·
            refine ⟨77463810208378544733802241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51642540138919029822534827 77463810208378544733802241)
            ·
              refine ⟨58097857656283908550351681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77463810208378544733802241 58097857656283908550351681)
              ·
                refine ⟨43573393242212931412763761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58097857656283908550351681 43573393242212931412763761)
                ·
                  refine ⟨32680044931659698559572821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43573393242212931412763761 32680044931659698559572821)
                  ·
                    refine ⟨191484638271443546247497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 32680044931659698559572821 191484638271443546247497)
                    ·
                      rfl

theorem cell23_1118745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_1118745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118745 prefixEnd_1118745 := by exact prefixLift 1118745
  have htrace : WordTrace (prefixWord ++ tailWord_1118745) baseStart_1118745 baseEnd_1118745 := by
    simpa [prefixWord, tailWord_1118745, baseEnd_1118745] using wordTrace_append hprefix tailTrace_1118745
  have hstable : (prefixWord ++ tailWord_1118745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118745).length < 2 ^ (prefixWord ++ tailWord_1118745).sum := by decide
  have hdescent : baseEnd_1118745 < baseStart_1118745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118766 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_1118766 : Nat := 118140960795 + 1118766 * 2 ^ 59
def prefixEnd_1118766 : Nat := 4983230072969 + 3 ^ 40 * 1118766 * 2
def baseEnd_1118766 : Nat := 63829410878675006286655

theorem tailTrace_1118766 : CollatzResearch.WordTrace tailWord_1118766 prefixEnd_1118766 63829410878675006286655 := by
  unfold tailWord_1118766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100593533113665858256019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27203165509939551244032101 5100593533113665858256019)
  ·
    refine ⟨7650890299670498787384029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5100593533113665858256019 7650890299670498787384029)
    ·
      refine ⟨2869083862376437045269011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7650890299670498787384029 2869083862376437045269011)
      ·
        refine ⟨4303625793564655567903517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869083862376437045269011 4303625793564655567903517)
        ·
          refine ⟨1613859672586745837963819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4303625793564655567903517 1613859672586745837963819)
          ·
            refine ⟨2420789508880118756945729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613859672586745837963819 2420789508880118756945729)
            ·
              refine ⟨1815592131660089067709297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420789508880118756945729 1815592131660089067709297)
              ·
                refine ⟨1361694098745066800781973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815592131660089067709297 1361694098745066800781973)
                ·
                  refine ⟨63829410878675006286655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1361694098745066800781973 63829410878675006286655)
                  ·
                    rfl

theorem cell23_1118766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_1118766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118766 prefixEnd_1118766 := by exact prefixLift 1118766
  have htrace : WordTrace (prefixWord ++ tailWord_1118766) baseStart_1118766 baseEnd_1118766 := by
    simpa [prefixWord, tailWord_1118766, baseEnd_1118766] using wordTrace_append hprefix tailTrace_1118766
  have hstable : (prefixWord ++ tailWord_1118766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118766).length < 2 ^ (prefixWord ++ tailWord_1118766).sum := by decide
  have hdescent : baseEnd_1118766 < baseStart_1118766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118816 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 1, 1, 4]
def baseStart_1118816 : Nat := 118140960795 + 1118816 * 2 ^ 59
def prefixEnd_1118816 : Nat := 4983230072969 + 3 ^ 40 * 1118816 * 2
def baseEnd_1118816 : Nat := 574490371940799860954665

theorem tailTrace_1118816 : CollatzResearch.WordTrace tailWord_1118816 prefixEnd_1118816 574490371940799860954665 := by
  unfold tailWord_1118816
  simp only [CollatzResearch.WordTrace]
  refine ⟨20403285957364092702684151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27204381276485456936912201 20403285957364092702684151)
  ·
    refine ⟨30604928936046139054026227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20403285957364092702684151 30604928936046139054026227)
    ·
      refine ⟨45907393404069208581039341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30604928936046139054026227 45907393404069208581039341)
      ·
        refine ⟨17215272526525953217889753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45907393404069208581039341 17215272526525953217889753)
        ·
          refine ⟨12911454394894464913417315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17215272526525953217889753 12911454394894464913417315)
          ·
            refine ⟨19367181592341697370125973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12911454394894464913417315 19367181592341697370125973)
            ·
              refine ⟨907836637141017064224655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19367181592341697370125973 907836637141017064224655)
              ·
                refine ⟨1361754955711525596336983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907836637141017064224655 1361754955711525596336983)
                ·
                  refine ⟨2042632433567288394505475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361754955711525596336983 2042632433567288394505475)
                  ·
                    refine ⟨3063948650350932591758213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2042632433567288394505475 3063948650350932591758213)
                    ·
                      refine ⟨574490371940799860954665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3063948650350932591758213 574490371940799860954665)
                      ·
                        rfl

theorem cell23_1118816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_1118816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118816 prefixEnd_1118816 := by exact prefixLift 1118816
  have htrace : WordTrace (prefixWord ++ tailWord_1118816) baseStart_1118816 baseEnd_1118816 := by
    simpa [prefixWord, tailWord_1118816, baseEnd_1118816] using wordTrace_append hprefix tailTrace_1118816
  have hstable : (prefixWord ++ tailWord_1118816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118816).length < 2 ^ (prefixWord ++ tailWord_1118816).sum := by decide
  have hdescent : baseEnd_1118816 < baseStart_1118816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118906 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2]
def baseStart_1118906 : Nat := 118140960795 + 1118906 * 2 ^ 59
def prefixEnd_1118906 : Nat := 4983230072969 + 3 ^ 40 * 1118906 * 2
def baseEnd_1118906 : Nat := 574536585199704508829251

theorem tailTrace_1118906 : CollatzResearch.WordTrace tailWord_1118906 prefixEnd_1118906 574536585199704508829251 := by
  unfold tailWord_1118906
  simp only [CollatzResearch.WordTrace]
  refine ⟨10202463621100532694036143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27206569656268087184096381 10202463621100532694036143)
  ·
    refine ⟨15303695431650799041054215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10202463621100532694036143 15303695431650799041054215)
    ·
      refine ⟨22955543147476198561581323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15303695431650799041054215 22955543147476198561581323)
      ·
        refine ⟨34433314721214297842371985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22955543147476198561581323 34433314721214297842371985)
        ·
          refine ⟨25824986040910723381778989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34433314721214297842371985 25824986040910723381778989)
          ·
            refine ⟨9684369765341521268167121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25824986040910723381778989 9684369765341521268167121)
            ·
              refine ⟨7263277324006140951125341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9684369765341521268167121 7263277324006140951125341)
              ·
                refine ⟨2723728996502302856672003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7263277324006140951125341 2723728996502302856672003)
                ·
                  refine ⟨4085593494753454285008005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723728996502302856672003 4085593494753454285008005)
                  ·
                    refine ⟨766048780266272678439001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085593494753454285008005 766048780266272678439001)
                    ·
                      refine ⟨574536585199704508829251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766048780266272678439001 574536585199704508829251)
                      ·
                        rfl

theorem cell23_1118906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_1118906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118906 prefixEnd_1118906 := by exact prefixLift 1118906
  have htrace : WordTrace (prefixWord ++ tailWord_1118906) baseStart_1118906 baseEnd_1118906 := by
    simpa [prefixWord, tailWord_1118906, baseEnd_1118906] using wordTrace_append hprefix tailTrace_1118906
  have hstable : (prefixWord ++ tailWord_1118906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118906).length < 2 ^ (prefixWord ++ tailWord_1118906).sum := by decide
  have hdescent : baseEnd_1118906 < baseStart_1118906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118909 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1118909 : Nat := 118140960795 + 1118909 * 2 ^ 59
def prefixEnd_1118909 : Nat := 4983230072969 + 3 ^ 40 * 1118909 * 2
def baseEnd_1118909 : Nat := 574538125641667997091737

theorem tailTrace_1118909 : CollatzResearch.WordTrace tailWord_1118909 prefixEnd_1118909 574538125641667997091737 := by
  unfold tailWord_1118909
  simp only [CollatzResearch.WordTrace]
  refine ⟨40809963903391262288503781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27206642602260841525669187 40809963903391262288503781)
  ·
    refine ⟨7651868231885861679094459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40809963903391262288503781 7651868231885861679094459)
    ·
      refine ⟨11477802347828792518641689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7651868231885861679094459 11477802347828792518641689)
      ·
        refine ⟨8608351760871594388981267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11477802347828792518641689 8608351760871594388981267)
        ·
          refine ⟨12912527641307391583471901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8608351760871594388981267 12912527641307391583471901)
          ·
            refine ⟨4842197865490271843801963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12912527641307391583471901 4842197865490271843801963)
            ·
              refine ⟨7263296798235407765702945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842197865490271843801963 7263296798235407765702945)
              ·
                refine ⟨5447472598676555824277209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7263296798235407765702945 5447472598676555824277209)
                ·
                  refine ⟨4085604449007416868207907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5447472598676555824277209 4085604449007416868207907)
                  ·
                    refine ⟨6128406673511125302311861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4085604449007416868207907 6128406673511125302311861)
                    ·
                      refine ⟨574538125641667997091737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6128406673511125302311861 574538125641667997091737)
                      ·
                        rfl

theorem cell23_1118909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1118909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1118909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1118909 prefixEnd_1118909 := by exact prefixLift 1118909
  have htrace : WordTrace (prefixWord ++ tailWord_1118909) baseStart_1118909 baseEnd_1118909 := by
    simpa [prefixWord, tailWord_1118909, baseEnd_1118909] using wordTrace_append hprefix tailTrace_1118909
  have hstable : (prefixWord ++ tailWord_1118909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118909).length < 2 ^ (prefixWord ++ tailWord_1118909).sum := by decide
  have hdescent : baseEnd_1118909 < baseStart_1118909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119009 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1119009 : Nat := 118140960795 + 1119009 * 2 ^ 59
def prefixEnd_1119009 : Nat := 4983230072969 + 3 ^ 40 * 1119009 * 2
def baseEnd_1119009 : Nat := 574589473707117605841277

theorem tailTrace_1119009 : CollatzResearch.WordTrace tailWord_1119009 prefixEnd_1119009 574589473707117605841277 := by
  unfold tailWord_1119009
  simp only [CollatzResearch.WordTrace]
  refine ⟨40813611203028979367144081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27209074135352652911429387 40813611203028979367144081)
  ·
    refine ⟨30610208402271734525358061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40813611203028979367144081 30610208402271734525358061)
    ·
      refine ⟨11478828150851900447009273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30610208402271734525358061 11478828150851900447009273)
      ·
        refine ⟨8609121113138925335256955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11478828150851900447009273 8609121113138925335256955)
        ·
          refine ⟨12913681669708388002885433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8609121113138925335256955 12913681669708388002885433)
          ·
            refine ⟨9685261252281291002164075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12913681669708388002885433 9685261252281291002164075)
            ·
              refine ⟨14527891878421936503246113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9685261252281291002164075 14527891878421936503246113)
              ·
                refine ⟨10895918908816452377434585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14527891878421936503246113 10895918908816452377434585)
                ·
                  refine ⟨8171939181612339283075939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10895918908816452377434585 8171939181612339283075939)
                  ·
                    refine ⟨12257908772418508924613909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8171939181612339283075939 12257908772418508924613909)
                    ·
                      refine ⟨574589473707117605841277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12257908772418508924613909 574589473707117605841277)
                      ·
                        rfl

theorem cell23_1119009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1119009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119009 prefixEnd_1119009 := by exact prefixLift 1119009
  have htrace : WordTrace (prefixWord ++ tailWord_1119009) baseStart_1119009 baseEnd_1119009 := by
    simpa [prefixWord, tailWord_1119009, baseEnd_1119009] using wordTrace_append hprefix tailTrace_1119009
  have hstable : (prefixWord ++ tailWord_1119009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119009).length < 2 ^ (prefixWord ++ tailWord_1119009).sum := by decide
  have hdescent : baseEnd_1119009 < baseStart_1119009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119016 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1119016 : Nat := 118140960795 + 1119016 * 2 ^ 59
def prefixEnd_1119016 : Nat := 4983230072969 + 3 ^ 40 * 1119016 * 2
def baseEnd_1119016 : Nat := 574593068071699078453745

theorem tailTrace_1119016 : CollatzResearch.WordTrace tailWord_1119016 prefixEnd_1119016 574593068071699078453745 := by
  unfold tailWord_1119016
  simp only [CollatzResearch.WordTrace]
  refine ⟨20406933257001809781324451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27209244342669079708432601 20406933257001809781324451)
  ·
    refine ⟨30610399885502714671986677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20406933257001809781324451 30610399885502714671986677)
    ·
      refine ⟨2869724989265879500498751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30610399885502714671986677 2869724989265879500498751)
      ·
        refine ⟨4304587483898819250748127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869724989265879500498751 4304587483898819250748127)
        ·
          refine ⟨6456881225848228876122191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304587483898819250748127 6456881225848228876122191)
          ·
            refine ⟨9685321838772343314183287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6456881225848228876122191 9685321838772343314183287)
            ·
              refine ⟨14527982758158514971274931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9685321838772343314183287 14527982758158514971274931)
              ·
                refine ⟨21791974137237772456912397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14527982758158514971274931 21791974137237772456912397)
                ·
                  refine ⟨8171990301464164671342149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21791974137237772456912397 8171990301464164671342149)
                  ·
                    refine ⟨1532248181524530875876653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8171990301464164671342149 1532248181524530875876653)
                    ·
                      refine ⟨574593068071699078453745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1532248181524530875876653 574593068071699078453745)
                      ·
                        rfl

theorem cell23_1119016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1119016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119016 prefixEnd_1119016 := by exact prefixLift 1119016
  have htrace : WordTrace (prefixWord ++ tailWord_1119016) baseStart_1119016 baseEnd_1119016 := by
    simpa [prefixWord, tailWord_1119016, baseEnd_1119016] using wordTrace_append hprefix tailTrace_1119016
  have hstable : (prefixWord ++ tailWord_1119016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119016).length < 2 ^ (prefixWord ++ tailWord_1119016).sum := by decide
  have hdescent : baseEnd_1119016 < baseStart_1119016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119057 : List Nat := [1, 2, 2, 1, 6, 1, 3, 2, 1, 4]
def baseStart_1119057 : Nat := 118140960795 + 1119057 * 2 ^ 59
def prefixEnd_1119057 : Nat := 4983230072969 + 3 ^ 40 * 1119057 * 2
def baseEnd_1119057 : Nat := 191538040259511139347019

theorem tailTrace_1119057 : CollatzResearch.WordTrace tailWord_1119057 prefixEnd_1119057 191538040259511139347019 := by
  unfold tailWord_1119057
  simp only [CollatzResearch.WordTrace]
  refine ⟨40815361906855083564891425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27210241271236722376594283 40815361906855083564891425)
  ·
    refine ⟨30611521430141312673668569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40815361906855083564891425 30611521430141312673668569)
    ·
      refine ⟨22958641072605984505251427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30611521430141312673668569 22958641072605984505251427)
      ·
        refine ⟨34437961608908976757877141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22958641072605984505251427 34437961608908976757877141)
        ·
          refine ⟨1614279450417608285525491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34437961608908976757877141 1614279450417608285525491)
          ·
            refine ⟨2421419175626412428288237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614279450417608285525491 2421419175626412428288237)
            ·
              refine ⟨908032190859904660608089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2421419175626412428288237 908032190859904660608089)
              ·
                refine ⟨681024143144928495456067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908032190859904660608089 681024143144928495456067)
                ·
                  refine ⟨1021536214717392743184101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681024143144928495456067 1021536214717392743184101)
                  ·
                    refine ⟨191538040259511139347019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021536214717392743184101 191538040259511139347019)
                    ·
                      rfl

theorem cell23_1119057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_1119057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119057 prefixEnd_1119057 := by exact prefixLift 1119057
  have htrace : WordTrace (prefixWord ++ tailWord_1119057) baseStart_1119057 baseEnd_1119057 := by
    simpa [prefixWord, tailWord_1119057, baseEnd_1119057] using wordTrace_append hprefix tailTrace_1119057
  have hstable : (prefixWord ++ tailWord_1119057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119057).length < 2 ^ (prefixWord ++ tailWord_1119057).sum := by decide
  have hdescent : baseEnd_1119057 < baseStart_1119057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119096 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 4, 4]
def baseStart_1119096 : Nat := 118140960795 + 1119096 * 2 ^ 59
def prefixEnd_1119096 : Nat := 4983230072969 + 3 ^ 40 * 1119096 * 2
def baseEnd_1119096 : Nat := 191544715508019588484459

theorem tailTrace_1119096 : CollatzResearch.WordTrace tailWord_1119096 prefixEnd_1119096 191544715508019588484459 := by
  unfold tailWord_1119096
  simp only [CollatzResearch.WordTrace]
  refine ⟨20408392176856896612780571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27211189569142528817040761 20408392176856896612780571)
  ·
    refine ⟨30612588265285344919170857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20408392176856896612780571 30612588265285344919170857)
    ·
      refine ⟨22959441198964008689378143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30612588265285344919170857 22959441198964008689378143)
      ·
        refine ⟨34439161798446013034067215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22959441198964008689378143 34439161798446013034067215)
        ·
          refine ⟨51658742697669019551100823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34439161798446013034067215 51658742697669019551100823)
          ·
            refine ⟨77488114046503529326651235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51658742697669019551100823 77488114046503529326651235)
            ·
              refine ⟨116232171069755293989976853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77488114046503529326651235 116232171069755293989976853)
              ·
                refine ⟨5448383018894779405780165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116232171069755293989976853 5448383018894779405780165)
                ·
                  refine ⟨1021571816042771138583781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5448383018894779405780165 1021571816042771138583781)
                  ·
                    refine ⟨191544715508019588484459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021571816042771138583781 191544715508019588484459)
                    ·
                      rfl

theorem cell23_1119096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_1119096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119096 prefixEnd_1119096 := by exact prefixLift 1119096
  have htrace : WordTrace (prefixWord ++ tailWord_1119096) baseStart_1119096 baseEnd_1119096 := by
    simpa [prefixWord, tailWord_1119096, baseEnd_1119096] using wordTrace_append hprefix tailTrace_1119096
  have hstable : (prefixWord ++ tailWord_1119096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119096).length < 2 ^ (prefixWord ++ tailWord_1119096).sum := by decide
  have hdescent : baseEnd_1119096 < baseStart_1119096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119109 : List Nat := [1, 3, 1, 1, 3, 14]
def baseStart_1119109 : Nat := 118140960795 + 1119109 * 2 ^ 59
def prefixEnd_1119109 : Nat := 4983230072969 + 3 ^ 40 * 1119109 * 2
def baseEnd_1119109 : Nat := 2364777044331552323419

theorem tailTrace_1119109 : CollatzResearch.WordTrace tailWord_1119109 prefixEnd_1119109 2364777044331552323419 := by
  unfold tailWord_1119109
  simp only [CollatzResearch.WordTrace]
  refine ⟨40817258502666696445784381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27211505668444464297189587 40817258502666696445784381)
  ·
    refine ⟨15306471938500011167169143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40817258502666696445784381 15306471938500011167169143)
    ·
      refine ⟨22959707907750016750753715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15306471938500011167169143 22959707907750016750753715)
      ·
        refine ⟨34439561861625025126130573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22959707907750016750753715 34439561861625025126130573)
        ·
          refine ⟨12914835698109384422298965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34439561861625025126130573 12914835698109384422298965)
          ·
            refine ⟨2364777044331552323419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 12914835698109384422298965 2364777044331552323419)
            ·
              rfl

theorem cell23_1119109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 14].length) (baseStart_1119109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119109 prefixEnd_1119109 := by exact prefixLift 1119109
  have htrace : WordTrace (prefixWord ++ tailWord_1119109) baseStart_1119109 baseEnd_1119109 := by
    simpa [prefixWord, tailWord_1119109, baseEnd_1119109] using wordTrace_append hprefix tailTrace_1119109
  have hstable : (prefixWord ++ tailWord_1119109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119109).length < 2 ^ (prefixWord ++ tailWord_1119109).sum := by decide
  have hdescent : baseEnd_1119109 < baseStart_1119109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119113 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 2, 4]
def baseStart_1119113 : Nat := 118140960795 + 1119113 * 2 ^ 59
def prefixEnd_1119113 : Nat := 4983230072969 + 3 ^ 40 * 1119113 * 2
def baseEnd_1119113 : Nat := 191547625231728399646933

theorem tailTrace_1119113 : CollatzResearch.WordTrace tailWord_1119113 prefixEnd_1119113 191547625231728399646933 := by
  unfold tailWord_1119113
  simp only [CollatzResearch.WordTrace]
  refine ⟨40817404394652205128929993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27211602929768136752619995 40817404394652205128929993)
  ·
    refine ⟨30613053295989153846697495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40817404394652205128929993 30613053295989153846697495)
    ·
      refine ⟨45919579943983730770046243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30613053295989153846697495 45919579943983730770046243)
      ·
        refine ⟨68879369915975596155069365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45919579943983730770046243 68879369915975596155069365)
        ·
          refine ⟨6457440929622712139537753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68879369915975596155069365 6457440929622712139537753)
          ·
            refine ⟨4843080697217034104653315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6457440929622712139537753 4843080697217034104653315)
            ·
              refine ⟨7264621045825551156979973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843080697217034104653315 7264621045825551156979973)
              ·
                refine ⟨1362116446092290841933745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7264621045825551156979973 1362116446092290841933745)
                ·
                  refine ⟨1021587334569218131450309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362116446092290841933745 1021587334569218131450309)
                  ·
                    refine ⟨191547625231728399646933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021587334569218131450309 191547625231728399646933)
                    ·
                      rfl

theorem cell23_1119113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 4].length) (baseStart_1119113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119113 prefixEnd_1119113 := by exact prefixLift 1119113
  have htrace : WordTrace (prefixWord ++ tailWord_1119113) baseStart_1119113 baseEnd_1119113 := by
    simpa [prefixWord, tailWord_1119113, baseEnd_1119113] using wordTrace_append hprefix tailTrace_1119113
  have hstable : (prefixWord ++ tailWord_1119113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119113).length < 2 ^ (prefixWord ++ tailWord_1119113).sum := by decide
  have hdescent : baseEnd_1119113 < baseStart_1119113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119114 : List Nat := [3, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_1119114 : Nat := 118140960795 + 1119114 * 2 ^ 59
def prefixEnd_1119114 : Nat := 4983230072969 + 3 ^ 40 * 1119114 * 2
def baseEnd_1119114 : Nat := 574643389175839695028295

theorem tailTrace_1119114 : CollatzResearch.WordTrace tailWord_1119114 prefixEnd_1119114 574643389175839695028295 := by
  unfold tailWord_1119114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10204360216912145574929099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27211627245099054866477597 10204360216912145574929099)
  ·
    refine ⟨15306540325368218362393649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10204360216912145574929099 15306540325368218362393649)
    ·
      refine ⟨11479905244026163771795237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15306540325368218362393649 11479905244026163771795237)
      ·
        refine ⟨2152482233254905707211607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11479905244026163771795237 2152482233254905707211607)
        ·
          refine ⟨3228723349882358560817411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152482233254905707211607 3228723349882358560817411)
          ·
            refine ⟨4843085024823537841226117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228723349882358560817411 4843085024823537841226117)
            ·
              refine ⟨908078442154413345229897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4843085024823537841226117 908078442154413345229897)
              ·
                refine ⟨681058831615810008922423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908078442154413345229897 681058831615810008922423)
                ·
                  refine ⟨1021588247423715013383635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681058831615810008922423 1021588247423715013383635)
                  ·
                    refine ⟨1532382371135572520075453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1021588247423715013383635 1532382371135572520075453)
                    ·
                      refine ⟨574643389175839695028295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1532382371135572520075453 574643389175839695028295)
                      ·
                        rfl

theorem cell23_1119114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_1119114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119114 prefixEnd_1119114 := by exact prefixLift 1119114
  have htrace : WordTrace (prefixWord ++ tailWord_1119114) baseStart_1119114 baseEnd_1119114 := by
    simpa [prefixWord, tailWord_1119114, baseEnd_1119114] using wordTrace_append hprefix tailTrace_1119114
  have hstable : (prefixWord ++ tailWord_1119114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119114).length < 2 ^ (prefixWord ++ tailWord_1119114).sum := by decide
  have hdescent : baseEnd_1119114 < baseStart_1119114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119133 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1119133 : Nat := 118140960795 + 1119133 * 2 ^ 59
def prefixEnd_1119133 : Nat := 4983230072969 + 3 ^ 40 * 1119133 * 2
def baseEnd_1119133 : Nat := 574653145308275120690707

theorem tailTrace_1119133 : CollatzResearch.WordTrace tailWord_1119133 prefixEnd_1119133 574653145308275120690707 := by
  unfold tailWord_1119133
  simp only [CollatzResearch.WordTrace]
  refine ⟨40818133854579748544658053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27212089236386499029772035 40818133854579748544658053)
  ·
    refine ⟨7653400097733702852123385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40818133854579748544658053 7653400097733702852123385)
    ·
      refine ⟨5740050073300277139092539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7653400097733702852123385 5740050073300277139092539)
      ·
        refine ⟨8610075109950415708638809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5740050073300277139092539 8610075109950415708638809)
        ·
          refine ⟨6457556332462811781479107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8610075109950415708638809 6457556332462811781479107)
          ·
            refine ⟨9686334498694217672218661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6457556332462811781479107 9686334498694217672218661)
            ·
              refine ⟨1816187718505165813540999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9686334498694217672218661 1816187718505165813540999)
              ·
                refine ⟨2724281577757748720311499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816187718505165813540999 2724281577757748720311499)
                ·
                  refine ⟨4086422366636623080467249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724281577757748720311499 4086422366636623080467249)
                  ·
                    refine ⟨3064816774977467310350437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4086422366636623080467249 3064816774977467310350437)
                    ·
                      refine ⟨574653145308275120690707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3064816774977467310350437 574653145308275120690707)
                      ·
                        rfl

theorem cell23_1119133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1119133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119133 prefixEnd_1119133 := by exact prefixLift 1119133
  have htrace : WordTrace (prefixWord ++ tailWord_1119133) baseStart_1119133 baseEnd_1119133 := by
    simpa [prefixWord, tailWord_1119133, baseEnd_1119133] using wordTrace_append hprefix tailTrace_1119133
  have hstable : (prefixWord ++ tailWord_1119133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119133).length < 2 ^ (prefixWord ++ tailWord_1119133).sum := by decide
  have hdescent : baseEnd_1119133 < baseStart_1119133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
