import V185TrunkScan23Chunk0930

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5509864 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_5509864 : Nat := 118140960795 + 5509864 * 2 ^ 59
def prefixEnd_5509864 : Nat := 4983230072969 + 3 ^ 40 * 5509864 * 2
def baseEnd_5509864 : Nat := 2829208572904535865460603

theorem tailTrace_5509864 : CollatzResearch.WordTrace tailWord_5509864 prefixEnd_5509864 2829208572904535865460603 := by
  unfold tailWord_5509864
  simp only [CollatzResearch.WordTrace]
  refine ⟨100480624855355606349344323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133974166473807475132459097 100480624855355606349344323)
  ·
    refine ⟨150720937283033409524016485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100480624855355606349344323 150720937283033409524016485)
    ·
      refine ⟨28260175740568764285753091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150720937283033409524016485 28260175740568764285753091)
      ·
        refine ⟨42390263610853146428629637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28260175740568764285753091 42390263610853146428629637)
        ·
          refine ⟨7948174427034964955368057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42390263610853146428629637 7948174427034964955368057)
          ·
            refine ⟨5961130820276223716526043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7948174427034964955368057 5961130820276223716526043)
            ·
              refine ⟨8941696230414335574789065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5961130820276223716526043 8941696230414335574789065)
              ·
                refine ⟨6706272172810751681091799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8941696230414335574789065 6706272172810751681091799)
                ·
                  refine ⟨10059408259216127521637699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706272172810751681091799 10059408259216127521637699)
                  ·
                    refine ⟨15089112388824191282456549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10059408259216127521637699 15089112388824191282456549)
                    ·
                      refine ⟨2829208572904535865460603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15089112388824191282456549 2829208572904535865460603)
                      ·
                        rfl

theorem cell23_5509864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_5509864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509864 prefixEnd_5509864 := by exact prefixLift 5509864
  have htrace : WordTrace (prefixWord ++ tailWord_5509864) baseStart_5509864 baseEnd_5509864 := by
    simpa [prefixWord, tailWord_5509864, baseEnd_5509864] using wordTrace_append hprefix tailTrace_5509864
  have hstable : (prefixWord ++ tailWord_5509864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509864).length < 2 ^ (prefixWord ++ tailWord_5509864).sum := by decide
  have hdescent : baseEnd_5509864 < baseStart_5509864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509880 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_5509880 : Nat := 118140960795 + 5509880 * 2 ^ 59
def prefixEnd_5509880 : Nat := 4983230072969 + 3 ^ 40 * 5509880 * 2
def baseEnd_5509880 : Nat := 2829216788595007802860529

theorem tailTrace_5509880 : CollatzResearch.WordTrace tailWord_5509880 prefixEnd_5509880 2829216788595007802860529 := by
  unfold tailWord_5509880
  simp only [CollatzResearch.WordTrace]
  refine ⟨100480916639326623715635547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133974555519102164954180729 100480916639326623715635547)
  ·
    refine ⟨150721374958989935573453321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100480916639326623715635547 150721374958989935573453321)
    ·
      refine ⟨113041031219242451680089991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150721374958989935573453321 113041031219242451680089991)
      ·
        refine ⟨169561546828863677520134987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113041031219242451680089991 169561546828863677520134987)
        ·
          refine ⟨254342320243295516280202481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169561546828863677520134987 254342320243295516280202481)
          ·
            refine ⟨190756740182471637210151861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254342320243295516280202481 190756740182471637210151861)
            ·
              refine ⟨17883444392106715988451737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190756740182471637210151861 17883444392106715988451737)
              ·
                refine ⟨13412583294080036991338803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17883444392106715988451737 13412583294080036991338803)
                ·
                  refine ⟨20118874941120055487008205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13412583294080036991338803 20118874941120055487008205)
                  ·
                    refine ⟨7544578102920020807628077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20118874941120055487008205 7544578102920020807628077)
                    ·
                      refine ⟨2829216788595007802860529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544578102920020807628077 2829216788595007802860529)
                      ·
                        rfl

theorem cell23_5509880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_5509880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509880 prefixEnd_5509880 := by exact prefixLift 5509880
  have htrace : WordTrace (prefixWord ++ tailWord_5509880) baseStart_5509880 baseEnd_5509880 := by
    simpa [prefixWord, tailWord_5509880, baseEnd_5509880] using wordTrace_append hprefix tailTrace_5509880
  have hstable : (prefixWord ++ tailWord_5509880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509880).length < 2 ^ (prefixWord ++ tailWord_5509880).sum := by decide
  have hdescent : baseEnd_5509880 < baseStart_5509880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509884 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_5509884 : Nat := 118140960795 + 5509884 * 2 ^ 59
def prefixEnd_5509884 : Nat := 4983230072969 + 3 ^ 40 * 5509884 * 2
def baseEnd_5509884 : Nat := 2829218842517625787210511

theorem tailTrace_5509884 : CollatzResearch.WordTrace tailWord_5509884 prefixEnd_5509884 2829218842517625787210511 := by
  unfold tailWord_5509884
  simp only [CollatzResearch.WordTrace]
  refine ⟨100480989585319378057208353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133974652780425837409611137 100480989585319378057208353)
  ·
    refine ⟨75360742188989533542906265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100480989585319378057208353 75360742188989533542906265)
    ·
      refine ⟨56520556641742150157179699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75360742188989533542906265 56520556641742150157179699)
      ·
        refine ⟨84780834962613225235769549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56520556641742150157179699 84780834962613225235769549)
        ·
          refine ⟨31792813110979959463413581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84780834962613225235769549 31792813110979959463413581)
          ·
            refine ⟨11922304916617484798780093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31792813110979959463413581 11922304916617484798780093)
            ·
              refine ⟨4470864343731556799542535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11922304916617484798780093 4470864343731556799542535)
              ·
                refine ⟨6706296515597335199313803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470864343731556799542535 6706296515597335199313803)
                ·
                  refine ⟨10059444773396002798970705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706296515597335199313803 10059444773396002798970705)
                  ·
                    refine ⟨7544583580047002099228029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10059444773396002798970705 7544583580047002099228029)
                    ·
                      refine ⟨2829218842517625787210511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544583580047002099228029 2829218842517625787210511)
                      ·
                        rfl

theorem cell23_5509884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_5509884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509884 prefixEnd_5509884 := by exact prefixLift 5509884
  have htrace : WordTrace (prefixWord ++ tailWord_5509884) baseStart_5509884 baseEnd_5509884 := by
    simpa [prefixWord, tailWord_5509884, baseEnd_5509884] using wordTrace_append hprefix tailTrace_5509884
  have hstable : (prefixWord ++ tailWord_5509884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509884).length < 2 ^ (prefixWord ++ tailWord_5509884).sum := by decide
  have hdescent : baseEnd_5509884 < baseStart_5509884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509893 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_5509893 : Nat := 118140960795 + 5509893 * 2 ^ 59
def prefixEnd_5509893 : Nat := 4983230072969 + 3 ^ 40 * 5509893 * 2
def baseEnd_5509893 : Nat := 2829223463843516251997969

theorem tailTrace_5509893 : CollatzResearch.WordTrace tailWord_5509893 prefixEnd_5509893 2829223463843516251997969 := by
  unfold tailWord_5509893
  simp only [CollatzResearch.WordTrace]
  refine ⟨200962307427606150651494333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133974871618404100434329555 200962307427606150651494333)
  ·
    refine ⟨75360865285352306494310375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200962307427606150651494333 75360865285352306494310375)
    ·
      refine ⟨113041297928028459741465563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75360865285352306494310375 113041297928028459741465563)
      ·
        refine ⟨169561946892042689612198345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113041297928028459741465563 169561946892042689612198345)
        ·
          refine ⟨127171460169032017209148759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169561946892042689612198345 127171460169032017209148759)
          ·
            refine ⟨190757190253548025813723139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127171460169032017209148759 190757190253548025813723139)
            ·
              refine ⟨286135785380322038720584709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190757190253548025813723139 286135785380322038720584709)
              ·
                refine ⟨53650459758810382260109633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286135785380322038720584709 53650459758810382260109633)
                ·
                  refine ⟨40237844819107786695082225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53650459758810382260109633 40237844819107786695082225)
                  ·
                    refine ⟨30178383614330840021311669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40237844819107786695082225 30178383614330840021311669)
                    ·
                      refine ⟨2829223463843516251997969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30178383614330840021311669 2829223463843516251997969)
                      ·
                        rfl

theorem cell23_5509893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_5509893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509893 prefixEnd_5509893 := by exact prefixLift 5509893
  have htrace : WordTrace (prefixWord ++ tailWord_5509893) baseStart_5509893 baseEnd_5509893 := by
    simpa [prefixWord, tailWord_5509893, baseEnd_5509893] using wordTrace_append hprefix tailTrace_5509893
  have hstable : (prefixWord ++ tailWord_5509893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509893).length < 2 ^ (prefixWord ++ tailWord_5509893).sum := by decide
  have hdescent : baseEnd_5509893 < baseStart_5509893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509897 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 3]
def baseStart_5509897 : Nat := 118140960795 + 5509897 * 2 ^ 59
def prefixEnd_5509897 : Nat := 4983230072969 + 3 ^ 40 * 5509897 * 2
def baseEnd_5509897 : Nat := 2829225517766134236347951

theorem tailTrace_5509897 : CollatzResearch.WordTrace tailWord_5509897 prefixEnd_5509897 2829225517766134236347951 := by
  unfold tailWord_5509897
  simp only [CollatzResearch.WordTrace]
  refine ⟨200962453319591659334639945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133974968879727772889759963 200962453319591659334639945)
  ·
    refine ⟨150721839989693744500979959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200962453319591659334639945 150721839989693744500979959)
    ·
      refine ⟨226082759984540616751469939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150721839989693744500979959 226082759984540616751469939)
      ·
        refine ⟨339124139976810925127204909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226082759984540616751469939 339124139976810925127204909)
        ·
          refine ⟨127171552491304096922701841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339124139976810925127204909 127171552491304096922701841)
          ·
            refine ⟨95378664368478072692026381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127171552491304096922701841 95378664368478072692026381)
            ·
              refine ⟨35766999138179277259509893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95378664368478072692026381 35766999138179277259509893)
              ·
                refine ⟨6706312338408614486158105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35766999138179277259509893 6706312338408614486158105)
                ·
                  refine ⟨5029734253806460864618579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6706312338408614486158105 5029734253806460864618579)
                  ·
                    refine ⟨7544601380709691296927869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5029734253806460864618579 7544601380709691296927869)
                    ·
                      refine ⟨2829225517766134236347951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544601380709691296927869 2829225517766134236347951)
                      ·
                        rfl

theorem cell23_5509897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 3].length) (baseStart_5509897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509897 prefixEnd_5509897 := by exact prefixLift 5509897
  have htrace : WordTrace (prefixWord ++ tailWord_5509897) baseStart_5509897 baseEnd_5509897 := by
    simpa [prefixWord, tailWord_5509897, baseEnd_5509897] using wordTrace_append hprefix tailTrace_5509897
  have hstable : (prefixWord ++ tailWord_5509897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509897).length < 2 ^ (prefixWord ++ tailWord_5509897).sum := by decide
  have hdescent : baseEnd_5509897 < baseStart_5509897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509903 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_5509903 : Nat := 118140960795 + 5509903 * 2 ^ 59
def prefixEnd_5509903 : Nat := 4983230072969 + 3 ^ 40 * 5509903 * 2
def baseEnd_5509903 : Nat := 2829228598650061212872923

theorem tailTrace_5509903 : CollatzResearch.WordTrace tailWord_5509903 prefixEnd_5509903 2829228598650061212872923 := by
  unfold tailWord_5509903
  simp only [CollatzResearch.WordTrace]
  refine ⟨200962672157569922359358363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133975114771713281572905575 200962672157569922359358363)
  ·
    refine ⟨301444008236354883539037545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200962672157569922359358363 301444008236354883539037545)
    ·
      refine ⟨226083006177266162654278159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301444008236354883539037545 226083006177266162654278159)
      ·
        refine ⟨339124509265899243981417239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226083006177266162654278159 339124509265899243981417239)
        ·
          refine ⟨508686763898848865972125859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339124509265899243981417239 508686763898848865972125859)
          ·
            refine ⟨763030145848273298958188789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508686763898848865972125859 763030145848273298958188789)
            ·
              refine ⟨71534076173275621777330199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 763030145848273298958188789 71534076173275621777330199)
              ·
                refine ⟨107301114259913432665995299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71534076173275621777330199 107301114259913432665995299)
                ·
                  refine ⟨160951671389870148998992949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107301114259913432665995299 160951671389870148998992949)
                  ·
                    refine ⟨15089219192800326468655589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160951671389870148998992949 15089219192800326468655589)
                    ·
                      refine ⟨2829228598650061212872923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15089219192800326468655589 2829228598650061212872923)
                      ·
                        rfl

theorem cell23_5509903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_5509903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509903 prefixEnd_5509903 := by exact prefixLift 5509903
  have htrace : WordTrace (prefixWord ++ tailWord_5509903) baseStart_5509903 baseEnd_5509903 := by
    simpa [prefixWord, tailWord_5509903, baseEnd_5509903] using wordTrace_append hprefix tailTrace_5509903
  have hstable : (prefixWord ++ tailWord_5509903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509903).length < 2 ^ (prefixWord ++ tailWord_5509903).sum := by decide
  have hdescent : baseEnd_5509903 < baseStart_5509903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509937 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 1, 4, 2]
def baseStart_5509937 : Nat := 118140960795 + 5509937 * 2 ^ 59
def prefixEnd_5509937 : Nat := 4983230072969 + 3 ^ 40 * 5509937 * 2
def baseEnd_5509937 : Nat := 2829246056992314079847767

theorem tailTrace_5509937 : CollatzResearch.WordTrace tailWord_5509937 prefixEnd_5509937 2829246056992314079847767 := by
  unfold tailWord_5509937
  simp only [CollatzResearch.WordTrace]
  refine ⟨200963912239446746166096065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133975941492964497444064043 200963912239446746166096065)
  ·
    refine ⟨150722934179585059624572049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200963912239446746166096065 150722934179585059624572049)
    ·
      refine ⟨113042200634688794718429037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150722934179585059624572049 113042200634688794718429037)
      ·
        refine ⟨42390825238008298019410889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113042200634688794718429037 42390825238008298019410889)
        ·
          refine ⟨31793118928506223514558167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42390825238008298019410889 31793118928506223514558167)
          ·
            refine ⟨47689678392759335271837251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31793118928506223514558167 47689678392759335271837251)
            ·
              refine ⟨71534517589139002907755877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47689678392759335271837251 71534517589139002907755877)
              ·
                refine ⟨13412722047963563045204227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71534517589139002907755877 13412722047963563045204227)
                ·
                  refine ⟨20119083071945344567806341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13412722047963563045204227 20119083071945344567806341)
                  ·
                    refine ⟨3772328075989752106463689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20119083071945344567806341 3772328075989752106463689)
                    ·
                      refine ⟨2829246056992314079847767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772328075989752106463689 2829246056992314079847767)
                      ·
                        rfl

theorem cell23_5509937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_5509937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509937 prefixEnd_5509937 := by exact prefixLift 5509937
  have htrace : WordTrace (prefixWord ++ tailWord_5509937) baseStart_5509937 baseEnd_5509937 := by
    simpa [prefixWord, tailWord_5509937, baseEnd_5509937] using wordTrace_append hprefix tailTrace_5509937
  have hstable : (prefixWord ++ tailWord_5509937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509937).length < 2 ^ (prefixWord ++ tailWord_5509937).sum := by decide
  have hdescent : baseEnd_5509937 < baseStart_5509937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509941 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_5509941 : Nat := 118140960795 + 5509941 * 2 ^ 59
def prefixEnd_5509941 : Nat := 4983230072969 + 3 ^ 40 * 5509941 * 2
def baseEnd_5509941 : Nat := 2829248110914932064197749

theorem tailTrace_5509941 : CollatzResearch.WordTrace tailWord_5509941 prefixEnd_5509941 2829248110914932064197749 := by
  unfold tailWord_5509941
  simp only [CollatzResearch.WordTrace]
  refine ⟨200964058131432254849241677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133976038754288169899494451 200964058131432254849241677)
  ·
    refine ⟨75361521799287095568465629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200964058131432254849241677 75361521799287095568465629)
    ·
      refine ⟨28260570674732660838174611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75361521799287095568465629 28260570674732660838174611)
      ·
        refine ⟨42390856012098991257261917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28260570674732660838174611 42390856012098991257261917)
        ·
          refine ⟨15896571004537121721473219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42390856012098991257261917 15896571004537121721473219)
          ·
            refine ⟨23844856506805682582209829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15896571004537121721473219 23844856506805682582209829)
            ·
              refine ⟨4470910595026065484164343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23844856506805682582209829 4470910595026065484164343)
              ·
                refine ⟨6706365892539098226246515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470910595026065484164343 6706365892539098226246515)
                ·
                  refine ⟨10059548838808647339369773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706365892539098226246515 10059548838808647339369773)
                  ·
                    refine ⟨3772330814553242752263665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10059548838808647339369773 3772330814553242752263665)
                    ·
                      refine ⟨2829248110914932064197749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772330814553242752263665 2829248110914932064197749)
                      ·
                        rfl

theorem cell23_5509941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_5509941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509941 prefixEnd_5509941 := by exact prefixLift 5509941
  have htrace : WordTrace (prefixWord ++ tailWord_5509941) baseStart_5509941 baseEnd_5509941 := by
    simpa [prefixWord, tailWord_5509941, baseEnd_5509941] using wordTrace_append hprefix tailTrace_5509941
  have hstable : (prefixWord ++ tailWord_5509941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509941).length < 2 ^ (prefixWord ++ tailWord_5509941).sum := by decide
  have hdescent : baseEnd_5509941 < baseStart_5509941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509943 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 9]
def baseStart_5509943 : Nat := 118140960795 + 5509943 * 2 ^ 59
def prefixEnd_5509943 : Nat := 4983230072969 + 3 ^ 40 * 5509943 * 2
def baseEnd_5509943 : Nat := 314361015319582339596971

theorem tailTrace_5509943 : CollatzResearch.WordTrace tailWord_5509943 prefixEnd_5509943 314361015319582339596971 := by
  unfold tailWord_5509943
  simp only [CollatzResearch.WordTrace]
  refine ⟨200964131077425009190814483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133976087384950006127209655 200964131077425009190814483)
  ·
    refine ⟨301446196616137513786221725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200964131077425009190814483 301446196616137513786221725)
    ·
      refine ⟨113042323731051567669833147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301446196616137513786221725 113042323731051567669833147)
      ·
        refine ⟨169563485596577351504749721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113042323731051567669833147 169563485596577351504749721)
        ·
          refine ⟨127172614197433013628562291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169563485596577351504749721 127172614197433013628562291)
          ·
            refine ⟨190758921296149520442843437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127172614197433013628562291 190758921296149520442843437)
            ·
              refine ⟨71534595486056070166066289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190758921296149520442843437 71534595486056070166066289)
              ·
                refine ⟨53650946614542052624549717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71534595486056070166066289 53650946614542052624549717)
                ·
                  refine ⟨314361015319582339596971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53650946614542052624549717 314361015319582339596971)
                  ·
                    rfl

theorem cell23_5509943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 9].length) (baseStart_5509943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509943 prefixEnd_5509943 := by exact prefixLift 5509943
  have htrace : WordTrace (prefixWord ++ tailWord_5509943) baseStart_5509943 baseEnd_5509943 := by
    simpa [prefixWord, tailWord_5509943, baseEnd_5509943] using wordTrace_append hprefix tailTrace_5509943
  have hstable : (prefixWord ++ tailWord_5509943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509943).length < 2 ^ (prefixWord ++ tailWord_5509943).sum := by decide
  have hdescent : baseEnd_5509943 < baseStart_5509943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509960 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 7]
def baseStart_5509960 : Nat := 118140960795 + 5509960 * 2 ^ 59
def prefixEnd_5509960 : Nat := 4983230072969 + 3 ^ 40 * 5509960 * 2
def baseEnd_5509960 : Nat := 314361985227485276651129

theorem tailTrace_5509960 : CollatzResearch.WordTrace tailWord_5509960 prefixEnd_5509960 314361985227485276651129 := by
  unfold tailWord_5509960
  simp only [CollatzResearch.WordTrace]
  refine ⟨100482375559181710547091667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133976500745575614062788889 100482375559181710547091667)
  ·
    refine ⟨150723563338772565820637501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100482375559181710547091667 150723563338772565820637501)
    ·
      refine ⟨56521336252039712182739063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150723563338772565820637501 56521336252039712182739063)
      ·
        refine ⟨84782004378059568274108595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56521336252039712182739063 84782004378059568274108595)
        ·
          refine ⟨127173006567089352411162893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84782004378059568274108595 127173006567089352411162893)
          ·
            refine ⟨47689877462658507154186085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127173006567089352411162893 47689877462658507154186085)
            ·
              refine ⟨8941852024248470091409891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47689877462658507154186085 8941852024248470091409891)
              ·
                refine ⟨13412778036372705137114837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8941852024248470091409891 13412778036372705137114837)
                ·
                  refine ⟨314361985227485276651129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13412778036372705137114837 314361985227485276651129)
                  ·
                    rfl

theorem cell23_5509960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 7].length) (baseStart_5509960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509960 prefixEnd_5509960 := by exact prefixLift 5509960
  have htrace : WordTrace (prefixWord ++ tailWord_5509960) baseStart_5509960 baseEnd_5509960 := by
    simpa [prefixWord, tailWord_5509960, baseEnd_5509960] using wordTrace_append hprefix tailTrace_5509960
  have hstable : (prefixWord ++ tailWord_5509960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509960).length < 2 ^ (prefixWord ++ tailWord_5509960).sum := by decide
  have hdescent : baseEnd_5509960 < baseStart_5509960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509997 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_5509997 : Nat := 118140960795 + 5509997 * 2 ^ 59
def prefixEnd_5509997 : Nat := 4983230072969 + 3 ^ 40 * 5509997 * 2
def baseEnd_5509997 : Nat := 2829276865831583845097491

theorem tailTrace_5509997 : CollatzResearch.WordTrace tailWord_5509997 prefixEnd_5509997 2829276865831583845097491 := by
  unfold tailWord_5509997
  simp only [CollatzResearch.WordTrace]
  refine ⟨200966100619229376413280245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133977400412819584275520163 200966100619229376413280245)
  ·
    refine ⟨18840571933052754038745023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200966100619229376413280245 18840571933052754038745023)
    ·
      refine ⟨28260857899579131058117535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18840571933052754038745023 28260857899579131058117535)
      ·
        refine ⟨42391286849368696587176303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28260857899579131058117535 42391286849368696587176303)
        ·
          refine ⟨63586930274053044880764455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42391286849368696587176303 63586930274053044880764455)
          ·
            refine ⟨95380395411079567321146683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63586930274053044880764455 95380395411079567321146683)
            ·
              refine ⟨143070593116619350981720025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95380395411079567321146683 143070593116619350981720025)
              ·
                refine ⟨107302944837464513236290019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143070593116619350981720025 107302944837464513236290019)
                ·
                  refine ⟨160954417256196769854435029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107302944837464513236290019 160954417256196769854435029)
                  ·
                    refine ⟨3772369154442111793463321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 160954417256196769854435029 3772369154442111793463321)
                    ·
                      refine ⟨2829276865831583845097491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772369154442111793463321 2829276865831583845097491)
                      ·
                        rfl

theorem cell23_5509997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_5509997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509997 prefixEnd_5509997 := by exact prefixLift 5509997
  have htrace : WordTrace (prefixWord ++ tailWord_5509997) baseStart_5509997 baseEnd_5509997 := by
    simpa [prefixWord, tailWord_5509997, baseEnd_5509997] using wordTrace_append hprefix tailTrace_5509997
  have hstable : (prefixWord ++ tailWord_5509997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509997).length < 2 ^ (prefixWord ++ tailWord_5509997).sum := by decide
  have hdescent : baseEnd_5509997 < baseStart_5509997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510027 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 2, 4, 2]
def baseStart_5510027 : Nat := 118140960795 + 5510027 * 2 ^ 59
def prefixEnd_5510027 : Nat := 4983230072969 + 3 ^ 40 * 5510027 * 2
def baseEnd_5510027 : Nat := 2829292270251218727722353

theorem tailTrace_5510027 : CollatzResearch.WordTrace tailWord_5510027 prefixEnd_5510027 2829292270251218727722353 := by
  unfold tailWord_5510027
  simp only [CollatzResearch.WordTrace]
  refine ⟨200967194809120691536872335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133978129872747127691248223 200967194809120691536872335)
  ·
    refine ⟨301450792213681037305308503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200967194809120691536872335 301450792213681037305308503)
    ·
      refine ⟨452176188320521555957962755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301450792213681037305308503 452176188320521555957962755)
      ·
        refine ⟨678264282480782333936944133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452176188320521555957962755 678264282480782333936944133)
        ·
          refine ⟨127174552965146687613177025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 678264282480782333936944133 127174552965146687613177025)
          ·
            refine ⟨95380914723860015709882769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127174552965146687613177025 95380914723860015709882769)
            ·
              refine ⟨71535686042895011782412077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95380914723860015709882769 71535686042895011782412077)
              ·
                refine ⟨26825882266085629418404529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71535686042895011782412077 26825882266085629418404529)
                ·
                  refine ⟨20119411699564222063803397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26825882266085629418404529 20119411699564222063803397)
                  ·
                    refine ⟨3772389693668291636963137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20119411699564222063803397 3772389693668291636963137)
                    ·
                      refine ⟨2829292270251218727722353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772389693668291636963137 2829292270251218727722353)
                      ·
                        rfl

theorem cell23_5510027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 4, 2].length) (baseStart_5510027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510027 prefixEnd_5510027 := by exact prefixLift 5510027
  have htrace : WordTrace (prefixWord ++ tailWord_5510027) baseStart_5510027 baseEnd_5510027 := by
    simpa [prefixWord, tailWord_5510027, baseEnd_5510027] using wordTrace_append hprefix tailTrace_5510027
  have hstable : (prefixWord ++ tailWord_5510027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510027).length < 2 ^ (prefixWord ++ tailWord_5510027).sum := by decide
  have hdescent : baseEnd_5510027 < baseStart_5510027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510071 : List Nat := [1, 1, 3, 1, 3, 1, 6, 2, 1, 4]
def baseStart_5510071 : Nat := 118140960795 + 5510071 * 2 ^ 59
def prefixEnd_5510071 : Nat := 4983230072969 + 3 ^ 40 * 5510071 * 2
def baseEnd_5510071 : Nat := 943104954466672185190717

theorem tailTrace_5510071 : CollatzResearch.WordTrace tailWord_5510071 prefixEnd_5510071 943104954466672185190717 := by
  unfold tailWord_5510071
  simp only [CollatzResearch.WordTrace]
  refine ⟨200968799620961287051474067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133979199747307524700982711 200968799620961287051474067)
  ·
    refine ⟨301453199431441930577211101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200968799620961287051474067 301453199431441930577211101)
    ·
      refine ⟨113044949786790723966454163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301453199431441930577211101 113044949786790723966454163)
      ·
        refine ⟨169567424680186085949681245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113044949786790723966454163 169567424680186085949681245)
        ·
          refine ⟨63587784255069782231130467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169567424680186085949681245 63587784255069782231130467)
          ·
            refine ⟨95381676382604673346695701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63587784255069782231130467 95381676382604673346695701)
            ·
              refine ⟨4471016080434594063126361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95381676382604673346695701 4471016080434594063126361)
              ·
                refine ⟨3353262060325945547344771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4471016080434594063126361 3353262060325945547344771)
                ·
                  refine ⟨5029893090488918321017157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353262060325945547344771 5029893090488918321017157)
                  ·
                    refine ⟨943104954466672185190717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5029893090488918321017157 943104954466672185190717)
                    ·
                      rfl

theorem cell23_5510071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_5510071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510071 prefixEnd_5510071 := by exact prefixLift 5510071
  have htrace : WordTrace (prefixWord ++ tailWord_5510071) baseStart_5510071 baseEnd_5510071 := by
    simpa [prefixWord, tailWord_5510071, baseEnd_5510071] using wordTrace_append hprefix tailTrace_5510071
  have hstable : (prefixWord ++ tailWord_5510071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510071).length < 2 ^ (prefixWord ++ tailWord_5510071).sum := by decide
  have hdescent : baseEnd_5510071 < baseStart_5510071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510090 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_5510090 : Nat := 118140960795 + 5510090 * 2 ^ 59
def prefixEnd_5510090 : Nat := 4983230072969 + 3 ^ 40 * 5510090 * 2
def baseEnd_5510090 : Nat := 2829324619532451981234563

theorem tailTrace_5510090 : CollatzResearch.WordTrace tailWord_5510090 prefixEnd_5510090 2829324619532451981234563 := by
  unfold tailWord_5510090
  simp only [CollatzResearch.WordTrace]
  refine ⟨50242373151973113324103931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133979661738594968864277149 50242373151973113324103931)
  ·
    refine ⟨75363559727959669986155897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50242373151973113324103931 75363559727959669986155897)
    ·
      refine ⟨56522669795969752489616923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75363559727959669986155897 56522669795969752489616923)
      ·
        refine ⟨84784004693954628734425385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56522669795969752489616923 84784004693954628734425385)
        ·
          refine ⟨63588003520465971550819039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84784004693954628734425385 63588003520465971550819039)
          ·
            refine ⟨95382005280698957326228559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63588003520465971550819039 95382005280698957326228559)
            ·
              refine ⟨143073007921048435989342839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95382005280698957326228559 143073007921048435989342839)
              ·
                refine ⟨214609511881572653984014259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143073007921048435989342839 214609511881572653984014259)
                ·
                  refine ⟨321914267822358980976021389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214609511881572653984014259 321914267822358980976021389)
                  ·
                    refine ⟨120717850433384617866008021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321914267822358980976021389 120717850433384617866008021)
                    ·
                      refine ⟨2829324619532451981234563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120717850433384617866008021 2829324619532451981234563)
                      ·
                        rfl

theorem cell23_5510090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_5510090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510090 prefixEnd_5510090 := by exact prefixLift 5510090
  have htrace : WordTrace (prefixWord ++ tailWord_5510090) baseStart_5510090 baseEnd_5510090 := by
    simpa [prefixWord, tailWord_5510090, baseEnd_5510090] using wordTrace_append hprefix tailTrace_5510090
  have hstable : (prefixWord ++ tailWord_5510090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510090).length < 2 ^ (prefixWord ++ tailWord_5510090).sum := by decide
  have hdescent : baseEnd_5510090 < baseStart_5510090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510094 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_5510094 : Nat := 118140960795 + 5510094 * 2 ^ 59
def prefixEnd_5510094 : Nat := 4983230072969 + 3 ^ 40 * 5510094 * 2
def baseEnd_5510094 : Nat := 2829326673455069965584545

theorem tailTrace_5510094 : CollatzResearch.WordTrace tailWord_5510094 prefixEnd_5510094 2829326673455069965584545 := by
  unfold tailWord_5510094
  simp only [CollatzResearch.WordTrace]
  refine ⟨25121204812484745247445167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133979758999918641319707557 25121204812484745247445167)
  ·
    refine ⟨37681807218727117871167751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25121204812484745247445167 37681807218727117871167751)
    ·
      refine ⟨56522710828090676806751627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37681807218727117871167751 56522710828090676806751627)
      ·
        refine ⟨84784066242136015210127441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56522710828090676806751627 84784066242136015210127441)
        ·
          refine ⟨63588049681602011407595581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84784066242136015210127441 63588049681602011407595581)
          ·
            refine ⟨23845518630600754277848343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63588049681602011407595581 23845518630600754277848343)
            ·
              refine ⟨35768277945901131416772515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23845518630600754277848343 35768277945901131416772515)
              ·
                refine ⟨53652416918851697125158773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35768277945901131416772515 53652416918851697125158773)
                ·
                  refine ⟨5029914086142346605483635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53652416918851697125158773 5029914086142346605483635)
                  ·
                    refine ⟨7544871129213519908225453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5029914086142346605483635 7544871129213519908225453)
                    ·
                      refine ⟨2829326673455069965584545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544871129213519908225453 2829326673455069965584545)
                      ·
                        rfl

theorem cell23_5510094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_5510094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510094 prefixEnd_5510094 := by exact prefixLift 5510094
  have htrace : WordTrace (prefixWord ++ tailWord_5510094) baseStart_5510094 baseEnd_5510094 := by
    simpa [prefixWord, tailWord_5510094, baseEnd_5510094] using wordTrace_append hprefix tailTrace_5510094
  have hstable : (prefixWord ++ tailWord_5510094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510094).length < 2 ^ (prefixWord ++ tailWord_5510094).sum := by decide
  have hdescent : baseEnd_5510094 < baseStart_5510094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510097 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 1, 5]
def baseStart_5510097 : Nat := 118140960795 + 5510097 * 2 ^ 59
def prefixEnd_5510097 : Nat := 4983230072969 + 3 ^ 40 * 5510097 * 2
def baseEnd_5510097 : Nat := 943109404632344484615677

theorem tailTrace_5510097 : CollatzResearch.WordTrace tailWord_5510097 prefixEnd_5510097 943109404632344484615677 := by
  unfold tailWord_5510097
  simp only [CollatzResearch.WordTrace]
  refine ⟨200969747918867093491920545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133979831945911395661280363 200969747918867093491920545)
  ·
    refine ⟨150727310939150320118940409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200969747918867093491920545 150727310939150320118940409)
    ·
      refine ⟨113045483204362740089205307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150727310939150320118940409 113045483204362740089205307)
      ·
        refine ⟨169568224806544110133807961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113045483204362740089205307 169568224806544110133807961)
        ·
          refine ⟨127176168604908082600355971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169568224806544110133807961 127176168604908082600355971)
          ·
            refine ⟨190764252907362123900533957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127176168604908082600355971 190764252907362123900533957)
            ·
              refine ⟨35768297420130398231350117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190764252907362123900533957 35768297420130398231350117)
              ·
                refine ⟨6706555766274449668378147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35768297420130398231350117 6706555766274449668378147)
                ·
                  refine ⟨10059833649411674502567221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706555766274449668378147 10059833649411674502567221)
                  ·
                    refine ⟨943109404632344484615677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10059833649411674502567221 943109404632344484615677)
                    ·
                      rfl

theorem cell23_5510097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_5510097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510097 prefixEnd_5510097 := by exact prefixLift 5510097
  have htrace : WordTrace (prefixWord ++ tailWord_5510097) baseStart_5510097 baseEnd_5510097 := by
    simpa [prefixWord, tailWord_5510097, baseEnd_5510097] using wordTrace_append hprefix tailTrace_5510097
  have hstable : (prefixWord ++ tailWord_5510097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510097).length < 2 ^ (prefixWord ++ tailWord_5510097).sum := by decide
  have hdescent : baseEnd_5510097 < baseStart_5510097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510104 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 1, 5, 2]
def baseStart_5510104 : Nat := 118140960795 + 5510104 * 2 ^ 59
def prefixEnd_5510104 : Nat := 4983230072969 + 3 ^ 40 * 5510104 * 2
def baseEnd_5510104 : Nat := 2829331808261614926459499

theorem tailTrace_5510104 : CollatzResearch.WordTrace tailWord_5510104 prefixEnd_5510104 2829331808261614926459499 := by
  unfold tailWord_5510104
  simp only [CollatzResearch.WordTrace]
  refine ⟨100485001614920866843712683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133980002153227822458283577 100485001614920866843712683)
  ·
    refine ⟨150727502422381300265569025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100485001614920866843712683 150727502422381300265569025)
    ·
      refine ⟨113045626816785975199176769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150727502422381300265569025 113045626816785975199176769)
      ·
        refine ⟨84784220112589481399382577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113045626816785975199176769 84784220112589481399382577)
        ·
          refine ⟨63588165084442111049536933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84784220112589481399382577 63588165084442111049536933)
          ·
            refine ⟨11922780953332895821788175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63588165084442111049536933 11922780953332895821788175)
            ·
              refine ⟨17884171429999343732682263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11922780953332895821788175 17884171429999343732682263)
              ·
                refine ⟨26826257144999015599023395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17884171429999343732682263 26826257144999015599023395)
                ·
                  refine ⟨40239385717498523398535093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26826257144999015599023395 40239385717498523398535093)
                  ·
                    refine ⟨3772442411015486568612665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40239385717498523398535093 3772442411015486568612665)
                    ·
                      refine ⟨2829331808261614926459499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772442411015486568612665 2829331808261614926459499)
                      ·
                        rfl

theorem cell23_5510104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_5510104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510104 prefixEnd_5510104 := by exact prefixLift 5510104
  have htrace : WordTrace (prefixWord ++ tailWord_5510104) baseStart_5510104 baseEnd_5510104 := by
    simpa [prefixWord, tailWord_5510104, baseEnd_5510104] using wordTrace_append hprefix tailTrace_5510104
  have hstable : (prefixWord ++ tailWord_5510104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510104).length < 2 ^ (prefixWord ++ tailWord_5510104).sum := by decide
  have hdescent : baseEnd_5510104 < baseStart_5510104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510137 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_5510137 : Nat := 118140960795 + 5510137 * 2 ^ 59
def prefixEnd_5510137 : Nat := 4983230072969 + 3 ^ 40 * 5510137 * 2
def baseEnd_5510137 : Nat := 2829348753123213297346847

theorem tailTrace_5510137 : CollatzResearch.WordTrace tailWord_5510137 prefixEnd_5510137 2829348753123213297346847 := by
  unfold tailWord_5510137
  simp only [CollatzResearch.WordTrace]
  refine ⟨200971206838722180323376665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133980804559148120215584443 200971206838722180323376665)
  ·
    refine ⟨150728405129041635242532499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200971206838722180323376665 150728405129041635242532499)
    ·
      refine ⟨226092607693562452863798749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150728405129041635242532499 226092607693562452863798749)
      ·
        refine ⟨84784727885085919823924531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226092607693562452863798749 84784727885085919823924531)
        ·
          refine ⟨127177091827628879735886797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84784727885085919823924531 127177091827628879735886797)
          ·
            refine ⟨47691409435360829900957549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127177091827628879735886797 47691409435360829900957549)
            ·
              refine ⟨17884278538260311212859081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47691409435360829900957549 17884278538260311212859081)
              ·
                refine ⟨13413208903695233409644311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17884278538260311212859081 13413208903695233409644311)
                ·
                  refine ⟨20119813355542850114466467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13413208903695233409644311 20119813355542850114466467)
                  ·
                    refine ⟨30179720033314275171699701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20119813355542850114466467 30179720033314275171699701)
                    ·
                      refine ⟨2829348753123213297346847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30179720033314275171699701 2829348753123213297346847)
                      ·
                        rfl

theorem cell23_5510137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_5510137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510137 prefixEnd_5510137 := by exact prefixLift 5510137
  have htrace : WordTrace (prefixWord ++ tailWord_5510137) baseStart_5510137 baseEnd_5510137 := by
    simpa [prefixWord, tailWord_5510137, baseEnd_5510137] using wordTrace_append hprefix tailTrace_5510137
  have hstable : (prefixWord ++ tailWord_5510137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510137).length < 2 ^ (prefixWord ++ tailWord_5510137).sum := by decide
  have hdescent : baseEnd_5510137 < baseStart_5510137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510151 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_5510151 : Nat := 118140960795 + 5510151 * 2 ^ 59
def prefixEnd_5510151 : Nat := 4983230072969 + 3 ^ 40 * 5510151 * 2
def baseEnd_5510151 : Nat := 2829355941852376242571783

theorem tailTrace_5510151 : CollatzResearch.WordTrace tailWord_5510151 prefixEnd_5510151 2829355941852376242571783 := by
  unfold tailWord_5510151
  simp only [CollatzResearch.WordTrace]
  refine ⟨200971717460671460714386307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133981144973780973809590871 200971717460671460714386307)
  ·
    refine ⟨301457576191007191071579461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200971717460671460714386307 301457576191007191071579461)
    ·
      refine ⟨56523295535813848325921149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301457576191007191071579461 56523295535813848325921149)
      ·
        refine ⟨21196235825930193122220431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56523295535813848325921149 21196235825930193122220431)
        ·
          refine ⟨31794353738895289683330647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21196235825930193122220431 31794353738895289683330647)
          ·
            refine ⟨47691530608342934524995971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31794353738895289683330647 47691530608342934524995971)
            ·
              refine ⟨71537295912514401787493957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47691530608342934524995971 71537295912514401787493957)
              ·
                refine ⟨13413242983596450335155117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71537295912514401787493957 13413242983596450335155117)
                ·
                  refine ⟨5029966118848668875683169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13413242983596450335155117 5029966118848668875683169)
                  ·
                    refine ⟨3772474589136501656762377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5029966118848668875683169 3772474589136501656762377)
                    ·
                      refine ⟨2829355941852376242571783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772474589136501656762377 2829355941852376242571783)
                      ·
                        rfl

theorem cell23_5510151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_5510151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510151 prefixEnd_5510151 := by exact prefixLift 5510151
  have htrace : WordTrace (prefixWord ++ tailWord_5510151) baseStart_5510151 baseEnd_5510151 := by
    simpa [prefixWord, tailWord_5510151, baseEnd_5510151] using wordTrace_append hprefix tailTrace_5510151
  have hstable : (prefixWord ++ tailWord_5510151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510151).length < 2 ^ (prefixWord ++ tailWord_5510151).sum := by decide
  have hdescent : baseEnd_5510151 < baseStart_5510151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510227 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 3]
def baseStart_5510227 : Nat := 118140960795 + 5510227 * 2 ^ 59
def prefixEnd_5510227 : Nat := 4983230072969 + 3 ^ 40 * 5510227 * 2
def baseEnd_5510227 : Nat := 2829394966382117945221433

theorem tailTrace_5510227 : CollatzResearch.WordTrace tailWord_5510227 prefixEnd_5510227 2829394966382117945221433 := by
  unfold tailWord_5510227
  simp only [CollatzResearch.WordTrace]
  refine ⟨200974489408396125694152935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133982992938930750462768623 200974489408396125694152935)
  ·
    refine ⟨301461734112594188541229403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200974489408396125694152935 301461734112594188541229403)
    ·
      refine ⟨452192601168891282811844105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301461734112594188541229403 452192601168891282811844105)
      ·
        refine ⟨339144450876668462108883079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452192601168891282811844105 339144450876668462108883079)
        ·
          refine ⟨508716676315002693163324619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339144450876668462108883079 508716676315002693163324619)
          ·
            refine ⟨763075014472504039744986929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508716676315002693163324619 763075014472504039744986929)
            ·
              refine ⟨572306260854378029808740197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763075014472504039744986929 572306260854378029808740197)
              ·
                refine ⟨107307423910195880589138787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572306260854378029808740197 107307423910195880589138787)
                ·
                  refine ⟨160961135865293820883708181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107307423910195880589138787 160961135865293820883708181)
                  ·
                    refine ⟨7545053243685647853923821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 160961135865293820883708181 7545053243685647853923821)
                    ·
                      refine ⟨2829394966382117945221433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7545053243685647853923821 2829394966382117945221433)
                      ·
                        rfl

theorem cell23_5510227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_5510227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510227 prefixEnd_5510227 := by exact prefixLift 5510227
  have htrace : WordTrace (prefixWord ++ tailWord_5510227) baseStart_5510227 baseEnd_5510227 := by
    simpa [prefixWord, tailWord_5510227, baseEnd_5510227] using wordTrace_append hprefix tailTrace_5510227
  have hstable : (prefixWord ++ tailWord_5510227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510227).length < 2 ^ (prefixWord ++ tailWord_5510227).sum := by decide
  have hdescent : baseEnd_5510227 < baseStart_5510227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510241 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_5510241 : Nat := 118140960795 + 5510241 * 2 ^ 59
def prefixEnd_5510241 : Nat := 4983230072969 + 3 ^ 40 * 5510241 * 2
def baseEnd_5510241 : Nat := 2829402155111280890446369

theorem tailTrace_5510241 : CollatzResearch.WordTrace tailWord_5510241 prefixEnd_5510241 2829402155111280890446369 := by
  unfold tailWord_5510241
  simp only [CollatzResearch.WordTrace]
  refine ⟨200975000030345406085162577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133983333353563604056775051 200975000030345406085162577)
  ·
    refine ⟨150731250022759054563871933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200975000030345406085162577 150731250022759054563871933)
    ·
      refine ⟨56524218758534645461451975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150731250022759054563871933 56524218758534645461451975)
      ·
        refine ⟨84786328137801968192177963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56524218758534645461451975 84786328137801968192177963)
        ·
          refine ⟨127179492206702952288266945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84786328137801968192177963 127179492206702952288266945)
          ·
            refine ⟨95384619155027214216200209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127179492206702952288266945 95384619155027214216200209)
            ·
              refine ⟨71538464366270410662150157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95384619155027214216200209 71538464366270410662150157)
              ·
                refine ⟨26826924137351403998306309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71538464366270410662150157 26826924137351403998306309)
                ·
                  refine ⟨5030048275753388249682433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26826924137351403998306309 5030048275753388249682433)
                  ·
                    refine ⟨3772536206815041187261825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5030048275753388249682433 3772536206815041187261825)
                    ·
                      refine ⟨2829402155111280890446369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772536206815041187261825 2829402155111280890446369)
                      ·
                        rfl

theorem cell23_5510241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_5510241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510241 prefixEnd_5510241 := by exact prefixLift 5510241
  have htrace : WordTrace (prefixWord ++ tailWord_5510241) baseStart_5510241 baseEnd_5510241 := by
    simpa [prefixWord, tailWord_5510241, baseEnd_5510241] using wordTrace_append hprefix tailTrace_5510241
  have hstable : (prefixWord ++ tailWord_5510241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510241).length < 2 ^ (prefixWord ++ tailWord_5510241).sum := by decide
  have hdescent : baseEnd_5510241 < baseStart_5510241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510254 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_5510254 : Nat := 118140960795 + 5510254 * 2 ^ 59
def prefixEnd_5510254 : Nat := 4983230072969 + 3 ^ 40 * 5510254 * 2
def baseEnd_5510254 : Nat := 2829408830359789339583809

theorem tailTrace_5510254 : CollatzResearch.WordTrace tailWord_5510254 prefixEnd_5510254 2829408830359789339583809 := by
  unfold tailWord_5510254
  simp only [CollatzResearch.WordTrace]
  refine ⟨25121934272412288663173227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133983649452865539536923877 25121934272412288663173227)
  ·
    refine ⟨37682901408618432994759841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25121934272412288663173227 37682901408618432994759841)
    ·
      refine ⟨28262176056463824746069881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37682901408618432994759841 28262176056463824746069881)
      ·
        refine ⟨21196632042347868559552411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28262176056463824746069881 21196632042347868559552411)
        ·
          refine ⟨31794948063521802839328617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21196632042347868559552411 31794948063521802839328617)
          ·
            refine ⟨23846211047641352129496463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31794948063521802839328617 23846211047641352129496463)
            ·
              refine ⟨35769316571462028194244695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23846211047641352129496463 35769316571462028194244695)
              ·
                refine ⟨53653974857193042291367043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35769316571462028194244695 53653974857193042291367043)
                ·
                  refine ⟨80480962285789563437050565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53653974857193042291367043 80480962285789563437050565)
                  ·
                    refine ⟨15090180428585543144446981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80480962285789563437050565 15090180428585543144446981)
                    ·
                      refine ⟨2829408830359789339583809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15090180428585543144446981 2829408830359789339583809)
                      ·
                        rfl

theorem cell23_5510254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_5510254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510254 prefixEnd_5510254 := by exact prefixLift 5510254
  have htrace : WordTrace (prefixWord ++ tailWord_5510254) baseStart_5510254 baseEnd_5510254 := by
    simpa [prefixWord, tailWord_5510254, baseEnd_5510254] using wordTrace_append hprefix tailTrace_5510254
  have hstable : (prefixWord ++ tailWord_5510254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510254).length < 2 ^ (prefixWord ++ tailWord_5510254).sum := by decide
  have hdescent : baseEnd_5510254 < baseStart_5510254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510258 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_5510258 : Nat := 118140960795 + 5510258 * 2 ^ 59
def prefixEnd_5510258 : Nat := 4983230072969 + 3 ^ 40 * 5510258 * 2
def baseEnd_5510258 : Nat := 2829410884282407323933791

theorem tailTrace_5510258 : CollatzResearch.WordTrace tailWord_5510258 prefixEnd_5510258 2829410884282407323933791 := by
  unfold tailWord_5510258
  simp only [CollatzResearch.WordTrace]
  refine ⟨50243905017820954497132857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133983746714189211992354285 50243905017820954497132857)
  ·
    refine ⟨37682928763365715872849643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50243905017820954497132857 37682928763365715872849643)
    ·
      refine ⟨56524393145048573809274465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37682928763365715872849643 56524393145048573809274465)
      ·
        refine ⟨42393294858786430356955849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56524393145048573809274465 42393294858786430356955849)
        ·
          refine ⟨31794971144089822767716887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42393294858786430356955849 31794971144089822767716887)
          ·
            refine ⟨47692456716134734151575331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31794971144089822767716887 47692456716134734151575331)
            ·
              refine ⟨71538685074202101227362997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47692456716134734151575331 71538685074202101227362997)
              ·
                refine ⟨6706751725706446990065281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71538685074202101227362997 6706751725706446990065281)
                ·
                  refine ⟨5030063794279835242548961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6706751725706446990065281 5030063794279835242548961)
                  ·
                    refine ⟨3772547845709876431911721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5030063794279835242548961 3772547845709876431911721)
                    ·
                      refine ⟨2829410884282407323933791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772547845709876431911721 2829410884282407323933791)
                      ·
                        rfl

theorem cell23_5510258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_5510258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510258 prefixEnd_5510258 := by exact prefixLift 5510258
  have htrace : WordTrace (prefixWord ++ tailWord_5510258) baseStart_5510258 baseEnd_5510258 := by
    simpa [prefixWord, tailWord_5510258, baseEnd_5510258] using wordTrace_append hprefix tailTrace_5510258
  have hstable : (prefixWord ++ tailWord_5510258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510258).length < 2 ^ (prefixWord ++ tailWord_5510258).sum := by decide
  have hdescent : baseEnd_5510258 < baseStart_5510258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510281 : List Nat := [1, 2, 1, 1, 4, 4, 2, 3, 5]
def baseStart_5510281 : Nat := 118140960795 + 5510281 * 2 ^ 59
def prefixEnd_5510281 : Nat := 4983230072969 + 3 ^ 40 * 5510281 * 2
def baseEnd_5510281 : Nat := 314380299370828970438465

theorem tailTrace_5510281 : CollatzResearch.WordTrace tailWord_5510281 prefixEnd_5510281 314380299370828970438465 := by
  unfold tailWord_5510281
  simp only [CollatzResearch.WordTrace]
  refine ⟨200976458950200492916618697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133984305966800328611079131 200976458950200492916618697)
  ·
    refine ⟨150732344212650369687464023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200976458950200492916618697 150732344212650369687464023)
    ·
      refine ⟨226098516318975554531196035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150732344212650369687464023 226098516318975554531196035)
      ·
        refine ⟨339147774478463331796794053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226098516318975554531196035 339147774478463331796794053)
        ·
          refine ⟨63590207714711874711898885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339147774478463331796794053 63590207714711874711898885)
          ·
            refine ⟨11923163946508476508481041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63590207714711874711898885 11923163946508476508481041)
            ·
              refine ⟨8942372959881357381360781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11923163946508476508481041 8942372959881357381360781)
              ·
                refine ⟨3353389859955509018010293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8942372959881357381360781 3353389859955509018010293)
                ·
                  refine ⟨314380299370828970438465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3353389859955509018010293 314380299370828970438465)
                  ·
                    rfl

theorem cell23_5510281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 5].length) (baseStart_5510281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510281 prefixEnd_5510281 := by exact prefixLift 5510281
  have htrace : WordTrace (prefixWord ++ tailWord_5510281) baseStart_5510281 baseEnd_5510281 := by
    simpa [prefixWord, tailWord_5510281, baseEnd_5510281] using wordTrace_append hprefix tailTrace_5510281
  have hstable : (prefixWord ++ tailWord_5510281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510281).length < 2 ^ (prefixWord ++ tailWord_5510281).sum := by decide
  have hdescent : baseEnd_5510281 < baseStart_5510281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510354 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 8]
def baseStart_5510354 : Nat := 118140960795 + 5510354 * 2 ^ 59
def prefixEnd_5510354 : Nat := 4983230072969 + 3 ^ 40 * 5510354 * 2
def baseEnd_5510354 : Nat := 314384464269470994259261

theorem tailTrace_5510354 : CollatzResearch.WordTrace tailWord_5510354 prefixEnd_5510354 314384464269470994259261 := by
  unfold tailWord_5510354
  simp only [CollatzResearch.WordTrace]
  refine ⟨50244780369734006596006529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133986080985957350922684077 50244780369734006596006529)
  ·
    refine ⟨37683585277300504947004897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50244780369734006596006529 37683585277300504947004897)
    ·
      refine ⟨28262688957975378710253673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37683585277300504947004897 28262688957975378710253673)
      ·
        refine ⟨21197016718481534032690255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28262688957975378710253673 21197016718481534032690255)
        ·
          refine ⟨31795525077722301049035383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21197016718481534032690255 31795525077722301049035383)
          ·
            refine ⟨47693287616583451573553075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31795525077722301049035383 47693287616583451573553075)
            ·
              refine ⟨71539931424875177360329613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47693287616583451573553075 71539931424875177360329613)
              ·
                refine ⟨26827474284328191510123605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71539931424875177360329613 26827474284328191510123605)
                ·
                  refine ⟨314384464269470994259261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26827474284328191510123605 314384464269470994259261)
                  ·
                    rfl

theorem cell23_5510354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_5510354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510354 prefixEnd_5510354 := by exact prefixLift 5510354
  have htrace : WordTrace (prefixWord ++ tailWord_5510354) baseStart_5510354 baseEnd_5510354 := by
    simpa [prefixWord, tailWord_5510354, baseEnd_5510354] using wordTrace_append hprefix tailTrace_5510354
  have hstable : (prefixWord ++ tailWord_5510354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510354).length < 2 ^ (prefixWord ++ tailWord_5510354).sum := by decide
  have hdescent : baseEnd_5510354 < baseStart_5510354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510391 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 6, 3, 2]
def baseStart_5510391 : Nat := 118140960795 + 5510391 * 2 ^ 59
def prefixEnd_5510391 : Nat := 4983230072969 + 3 ^ 40 * 5510391 * 2
def baseEnd_5510391 : Nat := 2829479177209455303570679

theorem tailTrace_5510391 : CollatzResearch.WordTrace tailWord_5510391 prefixEnd_5510391 2829479177209455303570679 := by
  unfold tailWord_5510391
  simp only [CollatzResearch.WordTrace]
  refine ⟨200980470979801981703123027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133986980653201321135415351 200980470979801981703123027)
  ·
    refine ⟨301470706469702972554684541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200980470979801981703123027 301470706469702972554684541)
    ·
      refine ⟨113051514926138614708006703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301470706469702972554684541 113051514926138614708006703)
      ·
        refine ⟨169577272389207922062010055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113051514926138614708006703 169577272389207922062010055)
        ·
          refine ⟨254365908583811883093015083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169577272389207922062010055 254365908583811883093015083)
          ·
            refine ⟨381548862875717824639522625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254365908583811883093015083 381548862875717824639522625)
            ·
              refine ⟨286161647156788368479641969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381548862875717824639522625 286161647156788368479641969)
              ·
                refine ⟨214621235367591276359731477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286161647156788368479641969 214621235367591276359731477)
                ·
                  refine ⟨10060370407855841079362413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214621235367591276359731477 10060370407855841079362413)
                  ·
                    refine ⟨3772638902945940404760905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10060370407855841079362413 3772638902945940404760905)
                    ·
                      refine ⟨2829479177209455303570679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772638902945940404760905 2829479177209455303570679)
                      ·
                        rfl

theorem cell23_5510391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_5510391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510391 prefixEnd_5510391 := by exact prefixLift 5510391
  have htrace : WordTrace (prefixWord ++ tailWord_5510391) baseStart_5510391 baseEnd_5510391 := by
    simpa [prefixWord, tailWord_5510391, baseEnd_5510391] using wordTrace_append hprefix tailTrace_5510391
  have hstable : (prefixWord ++ tailWord_5510391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510391).length < 2 ^ (prefixWord ++ tailWord_5510391).sum := by decide
  have hdescent : baseEnd_5510391 < baseStart_5510391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510421 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_5510421 : Nat := 118140960795 + 5510421 * 2 ^ 59
def prefixEnd_5510421 : Nat := 4983230072969 + 3 ^ 40 * 5510421 * 2
def baseEnd_5510421 : Nat := 2829494581629090186195541

theorem tailTrace_5510421 : CollatzResearch.WordTrace tailWord_5510421 prefixEnd_5510421 2829494581629090186195541 := by
  unfold tailWord_5510421
  simp only [CollatzResearch.WordTrace]
  refine ⟨200981565169693296826715117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133987710113128864551143411 200981565169693296826715117)
  ·
    refine ⟨75368086938634986310018169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200981565169693296826715117 75368086938634986310018169)
    ·
      refine ⟨56526065203976239732513627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75368086938634986310018169 56526065203976239732513627)
      ·
        refine ⟨84789097805964359598770441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56526065203976239732513627 84789097805964359598770441)
        ·
          refine ⟨63591823354473269699077831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84789097805964359598770441 63591823354473269699077831)
          ·
            refine ⟨95387735031709904548616747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63591823354473269699077831 95387735031709904548616747)
            ·
              refine ⟨143081602547564856822925121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95387735031709904548616747 143081602547564856822925121)
              ·
                refine ⟨107311201910673642617193841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143081602547564856822925121 107311201910673642617193841)
                ·
                  refine ⟨80483401433005231962895381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107311201910673642617193841 80483401433005231962895381)
                  ·
                    refine ⟨3772659442172120248260721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80483401433005231962895381 3772659442172120248260721)
                    ·
                      refine ⟨2829494581629090186195541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772659442172120248260721 2829494581629090186195541)
                      ·
                        rfl

theorem cell23_5510421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_5510421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510421 prefixEnd_5510421 := by exact prefixLift 5510421
  have htrace : WordTrace (prefixWord ++ tailWord_5510421) baseStart_5510421 baseEnd_5510421 := by
    simpa [prefixWord, tailWord_5510421, baseEnd_5510421] using wordTrace_append hprefix tailTrace_5510421
  have hstable : (prefixWord ++ tailWord_5510421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510421).length < 2 ^ (prefixWord ++ tailWord_5510421).sum := by decide
  have hdescent : baseEnd_5510421 < baseStart_5510421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510442 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5510442 : Nat := 118140960795 + 5510442 * 2 ^ 59
def prefixEnd_5510442 : Nat := 4983230072969 + 3 ^ 40 * 5510442 * 2
def baseEnd_5510442 : Nat := 2829505364722834604032945

theorem tailTrace_5510442 : CollatzResearch.WordTrace tailWord_5510442 prefixEnd_5510442 2829505364722834604032945 := by
  unfold tailWord_5510442
  simp only [CollatzResearch.WordTrace]
  refine ⟨50245582775654304353307395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133988220735078144942153053 50245582775654304353307395)
  ·
    refine ⟨75368374163481456529961093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50245582775654304353307395 75368374163481456529961093)
    ·
      refine ⟨14131570155652773099367705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75368374163481456529961093 14131570155652773099367705)
      ·
        refine ⟨10598677616739579824525779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14131570155652773099367705 10598677616739579824525779)
        ·
          refine ⟨15898016425109369736788669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10598677616739579824525779 15898016425109369736788669)
          ·
            refine ⟨5961756159416013651295751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15898016425109369736788669 5961756159416013651295751)
            ·
              refine ⟨8942634239124020476943627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5961756159416013651295751 8942634239124020476943627)
              ·
                refine ⟨13413951358686030715415441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8942634239124020476943627 13413951358686030715415441)
                ·
                  refine ⟨10060463519014523036561581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13413951358686030715415441 10060463519014523036561581)
                  ·
                    refine ⟨3772673819630446138710593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10060463519014523036561581 3772673819630446138710593)
                    ·
                      refine ⟨2829505364722834604032945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772673819630446138710593 2829505364722834604032945)
                      ·
                        rfl

theorem cell23_5510442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5510442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510442 prefixEnd_5510442 := by exact prefixLift 5510442
  have htrace : WordTrace (prefixWord ++ tailWord_5510442) baseStart_5510442 baseEnd_5510442 := by
    simpa [prefixWord, tailWord_5510442, baseEnd_5510442] using wordTrace_append hprefix tailTrace_5510442
  have hstable : (prefixWord ++ tailWord_5510442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510442).length < 2 ^ (prefixWord ++ tailWord_5510442).sum := by decide
  have hdescent : baseEnd_5510442 < baseStart_5510442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510451 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 4]
def baseStart_5510451 : Nat := 118140960795 + 5510451 * 2 ^ 59
def prefixEnd_5510451 : Nat := 4983230072969 + 3 ^ 40 * 5510451 * 2
def baseEnd_5510451 : Nat := 2829509986048725068820403

theorem tailTrace_5510451 : CollatzResearch.WordTrace tailWord_5510451 prefixEnd_5510451 2829509986048725068820403 := by
  unfold tailWord_5510451
  simp only [CollatzResearch.WordTrace]
  refine ⟨200982659359584611950307207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133988439573056407966871471 200982659359584611950307207)
  ·
    refine ⟨301473989039376917925460811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200982659359584611950307207 301473989039376917925460811)
    ·
      refine ⟨452210983559065376888191217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301473989039376917925460811 452210983559065376888191217)
      ·
        refine ⟨339158237669299032666143413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452210983559065376888191217 339158237669299032666143413)
        ·
          refine ⟨31796084781496784312450945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 339158237669299032666143413 31796084781496784312450945)
          ·
            refine ⟨23847063586122588234338209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31796084781496784312450945 23847063586122588234338209)
            ·
              refine ⟨17885297689591941175753657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23847063586122588234338209 17885297689591941175753657)
              ·
                refine ⟨13413973267193955881815243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17885297689591941175753657 13413973267193955881815243)
                ·
                  refine ⟨20120959900790933822722865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13413973267193955881815243 20120959900790933822722865)
                  ·
                    refine ⟨15090719925593200367042149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20120959900790933822722865 15090719925593200367042149)
                    ·
                      refine ⟨2829509986048725068820403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15090719925593200367042149 2829509986048725068820403)
                      ·
                        rfl

theorem cell23_5510451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_5510451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510451 prefixEnd_5510451 := by exact prefixLift 5510451
  have htrace : WordTrace (prefixWord ++ tailWord_5510451) baseStart_5510451 baseEnd_5510451 := by
    simpa [prefixWord, tailWord_5510451, baseEnd_5510451] using wordTrace_append hprefix tailTrace_5510451
  have hstable : (prefixWord ++ tailWord_5510451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510451).length < 2 ^ (prefixWord ++ tailWord_5510451).sum := by decide
  have hdescent : baseEnd_5510451 < baseStart_5510451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510458 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_5510458 : Nat := 118140960795 + 5510458 * 2 ^ 59
def prefixEnd_5510458 : Nat := 4983230072969 + 3 ^ 40 * 5510458 * 2
def baseEnd_5510458 : Nat := 2829513580413306541432871

theorem tailTrace_5510458 : CollatzResearch.WordTrace tailWord_5510458 prefixEnd_5510458 2829513580413306541432871 := by
  unfold tailWord_5510458
  simp only [CollatzResearch.WordTrace]
  refine ⟨50245728667639813036453007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133988609780372834763874685 50245728667639813036453007)
  ·
    refine ⟨75368593001459719554679511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50245728667639813036453007 75368593001459719554679511)
    ·
      refine ⟨113052889502189579332019267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75368593001459719554679511 113052889502189579332019267)
      ·
        refine ⟨169579334253284368998028901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113052889502189579332019267 169579334253284368998028901)
        ·
          refine ⟨31796125172490819187130419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169579334253284368998028901 31796125172490819187130419)
          ·
            refine ⟨47694187758736228780695629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31796125172490819187130419 47694187758736228780695629)
            ·
              refine ⟨17885320409526085792760861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47694187758736228780695629 17885320409526085792760861)
              ·
                refine ⟨6706995153572282172285323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17885320409526085792760861 6706995153572282172285323)
                ·
                  refine ⟨10060492730358423258427985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706995153572282172285323 10060492730358423258427985)
                  ·
                    refine ⟨7545369547768817443820989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10060492730358423258427985 7545369547768817443820989)
                    ·
                      refine ⟨2829513580413306541432871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7545369547768817443820989 2829513580413306541432871)
                      ·
                        rfl

theorem cell23_5510458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_5510458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510458 prefixEnd_5510458 := by exact prefixLift 5510458
  have htrace : WordTrace (prefixWord ++ tailWord_5510458) baseStart_5510458 baseEnd_5510458 := by
    simpa [prefixWord, tailWord_5510458, baseEnd_5510458] using wordTrace_append hprefix tailTrace_5510458
  have hstable : (prefixWord ++ tailWord_5510458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510458).length < 2 ^ (prefixWord ++ tailWord_5510458).sum := by decide
  have hdescent : baseEnd_5510458 < baseStart_5510458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510465 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 2, 4]
def baseStart_5510465 : Nat := 118140960795 + 5510465 * 2 ^ 59
def prefixEnd_5510465 : Nat := 4983230072969 + 3 ^ 40 * 5510465 * 2
def baseEnd_5510465 : Nat := 943172391592629338015113

theorem tailTrace_5510465 : CollatzResearch.WordTrace tailWord_5510465 prefixEnd_5510465 943172391592629338015113 := by
  unfold tailWord_5510465
  simp only [CollatzResearch.WordTrace]
  refine ⟨200983169981533892341316849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133988779987689261560877899 200983169981533892341316849)
  ·
    refine ⟨150737377486150419255987637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200983169981533892341316849 150737377486150419255987637)
    ·
      refine ⟨14131629139326601805248841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150737377486150419255987637 14131629139326601805248841)
      ·
        refine ⟨10598721854494951353936631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14131629139326601805248841 10598721854494951353936631)
        ·
          refine ⟨15898082781742427030904947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10598721854494951353936631 15898082781742427030904947)
          ·
            refine ⟨23847124172613640546357421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15898082781742427030904947 23847124172613640546357421)
            ·
              refine ⟨8942671564730115204884033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23847124172613640546357421 8942671564730115204884033)
              ·
                refine ⟨6707003673547586403663025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8942671564730115204884033 6707003673547586403663025)
                ·
                  refine ⟨5030252755160689802747269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6707003673547586403663025 5030252755160689802747269)
                  ·
                    refine ⟨943172391592629338015113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5030252755160689802747269 943172391592629338015113)
                    ·
                      rfl

theorem cell23_5510465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_5510465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510465 prefixEnd_5510465 := by exact prefixLift 5510465
  have htrace : WordTrace (prefixWord ++ tailWord_5510465) baseStart_5510465 baseEnd_5510465 := by
    simpa [prefixWord, tailWord_5510465, baseEnd_5510465] using wordTrace_append hprefix tailTrace_5510465
  have hstable : (prefixWord ++ tailWord_5510465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510465).length < 2 ^ (prefixWord ++ tailWord_5510465).sum := by decide
  have hdescent : baseEnd_5510465 < baseStart_5510465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510474 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_5510474 : Nat := 118140960795 + 5510474 * 2 ^ 59
def prefixEnd_5510474 : Nat := 4983230072969 + 3 ^ 40 * 5510474 * 2
def baseEnd_5510474 : Nat := 943173932034592826277599

theorem tailTrace_5510474 : CollatzResearch.WordTrace tailWord_5510474 prefixEnd_5510474 943173932034592826277599 := by
  unfold tailWord_5510474
  simp only [CollatzResearch.WordTrace]
  refine ⟨50245874559625321719598619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133988998825667524585596317 50245874559625321719598619)
  ·
    refine ⟨75368811839437982579397929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50245874559625321719598619 75368811839437982579397929)
    ·
      refine ⟨56526608879578486934548447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75368811839437982579397929 56526608879578486934548447)
      ·
        refine ⟨84789913319367730401822671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56526608879578486934548447 84789913319367730401822671)
        ·
          refine ⟨127184869979051595602734007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84789913319367730401822671 127184869979051595602734007)
          ·
            refine ⟨190777304968577393404101011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127184869979051595602734007 190777304968577393404101011)
            ·
              refine ⟨286165957452866090106151517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190777304968577393404101011 286165957452866090106151517)
              ·
                refine ⟨107312234044824783789806819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286165957452866090106151517 107312234044824783789806819)
                ·
                  refine ⟨160968351067237175684710229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107312234044824783789806819 160968351067237175684710229)
                  ·
                    refine ⟨943173932034592826277599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 160968351067237175684710229 943173932034592826277599)
                    ·
                      rfl

theorem cell23_5510474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_5510474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510474 prefixEnd_5510474 := by exact prefixLift 5510474
  have htrace : WordTrace (prefixWord ++ tailWord_5510474) baseStart_5510474 baseEnd_5510474 := by
    simpa [prefixWord, tailWord_5510474, baseEnd_5510474] using wordTrace_append hprefix tailTrace_5510474
  have hstable : (prefixWord ++ tailWord_5510474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510474).length < 2 ^ (prefixWord ++ tailWord_5510474).sum := by decide
  have hdescent : baseEnd_5510474 < baseStart_5510474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510506 : List Nat := [3, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_5510506 : Nat := 118140960795 + 5510506 * 2 ^ 59
def prefixEnd_5510506 : Nat := 4983230072969 + 3 ^ 40 * 5510506 * 2
def baseEnd_5510506 : Nat := 2829538227484722353632651

theorem tailTrace_5510506 : CollatzResearch.WordTrace tailWord_5510506 prefixEnd_5510506 2829538227484722353632651 := by
  unfold tailWord_5510506
  simp only [CollatzResearch.WordTrace]
  refine ⟨50246166343596339085889843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133989776916256904229039581 50246166343596339085889843)
  ·
    refine ⟨75369249515394508628834765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50246166343596339085889843 75369249515394508628834765)
    ·
      refine ⟨28263468568272940735813037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75369249515394508628834765 28263468568272940735813037)
      ·
        refine ⟨10598800713102352775929889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28263468568272940735813037 10598800713102352775929889)
        ·
          refine ⟨7949100534826764581947417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10598800713102352775929889 7949100534826764581947417)
          ·
            refine ⟨5961825401120073436460563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7949100534826764581947417 5961825401120073436460563)
            ·
              refine ⟨8942738101680110154690845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5961825401120073436460563 8942738101680110154690845)
              ·
                refine ⟨3353526788130041308009067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8942738101680110154690845 3353526788130041308009067)
                ·
                  refine ⟨5030290182195061962013601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353526788130041308009067 5030290182195061962013601)
                  ·
                    refine ⟨3772717636646296471510201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5030290182195061962013601 3772717636646296471510201)
                    ·
                      refine ⟨2829538227484722353632651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772717636646296471510201 2829538227484722353632651)
                      ·
                        rfl

theorem cell23_5510506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_5510506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510506 prefixEnd_5510506 := by exact prefixLift 5510506
  have htrace : WordTrace (prefixWord ++ tailWord_5510506) baseStart_5510506 baseEnd_5510506 := by
    simpa [prefixWord, tailWord_5510506, baseEnd_5510506] using wordTrace_append hprefix tailTrace_5510506
  have hstable : (prefixWord ++ tailWord_5510506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510506).length < 2 ^ (prefixWord ++ tailWord_5510506).sum := by decide
  have hdescent : baseEnd_5510506 < baseStart_5510506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510545 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 2, 2, 2]
def baseStart_5510545 : Nat := 118140960795 + 5510545 * 2 ^ 59
def prefixEnd_5510545 : Nat := 4983230072969 + 3 ^ 40 * 5510545 * 2
def baseEnd_5510545 : Nat := 2829558253230247701044971

theorem tailTrace_5510545 : CollatzResearch.WordTrace tailWord_5510545 prefixEnd_5510545 2829558253230247701044971 := by
  unfold tailWord_5510545
  simp only [CollatzResearch.WordTrace]
  refine ⟨200986087821244066004229089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133990725214162710669486059 200986087821244066004229089)
  ·
    refine ⟨150739565865933049503171817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200986087821244066004229089 150739565865933049503171817)
    ·
      refine ⟨113054674399449787127378863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150739565865933049503171817 113054674399449787127378863)
      ·
        refine ⟨169582011599174680691068295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113054674399449787127378863 169582011599174680691068295)
        ·
          refine ⟨254373017398762021036602443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169582011599174680691068295 254373017398762021036602443)
          ·
            refine ⟨381559526098143031554903665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254373017398762021036602443 381559526098143031554903665)
            ·
              refine ⟨286169644573607273666177749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381559526098143031554903665 286169644573607273666177749)
              ·
                refine ⟨6707101044693920476551041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 286169644573607273666177749 6707101044693920476551041)
                ·
                  refine ⟨5030325783520440357413281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6707101044693920476551041 5030325783520440357413281)
                  ·
                    refine ⟨3772744337640330268059961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5030325783520440357413281 3772744337640330268059961)
                    ·
                      refine ⟨2829558253230247701044971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772744337640330268059961 2829558253230247701044971)
                      ·
                        rfl

theorem cell23_5510545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_5510545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510545 prefixEnd_5510545 := by exact prefixLift 5510545
  have htrace : WordTrace (prefixWord ++ tailWord_5510545) baseStart_5510545 baseEnd_5510545 := by
    simpa [prefixWord, tailWord_5510545, baseEnd_5510545] using wordTrace_append hprefix tailTrace_5510545
  have hstable : (prefixWord ++ tailWord_5510545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510545).length < 2 ^ (prefixWord ++ tailWord_5510545).sum := by decide
  have hdescent : baseEnd_5510545 < baseStart_5510545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510548 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_5510548 : Nat := 118140960795 + 5510548 * 2 ^ 59
def prefixEnd_5510548 : Nat := 4983230072969 + 3 ^ 40 * 5510548 * 2
def baseEnd_5510548 : Nat := 2829559793672211189307457

theorem tailTrace_5510548 : CollatzResearch.WordTrace tailWord_5510548 prefixEnd_5510548 2829559793672211189307457 := by
  unfold tailWord_5510548
  simp only [CollatzResearch.WordTrace]
  refine ⟨100493098620116598758294149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133990798160155465011058865 100493098620116598758294149)
  ·
    refine ⟨18842455991271862267180153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100493098620116598758294149 18842455991271862267180153)
    ·
      refine ⟨14131841993453896700385115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18842455991271862267180153 14131841993453896700385115)
      ·
        refine ⟨21197762990180845050577673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14131841993453896700385115 21197762990180845050577673)
        ·
          refine ⟨15898322242635633787933255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21197762990180845050577673 15898322242635633787933255)
          ·
            refine ⟨23847483363953450681899883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15898322242635633787933255 23847483363953450681899883)
            ·
              refine ⟨35771225045930176022849825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23847483363953450681899883 35771225045930176022849825)
              ·
                refine ⟨26828418784447632017137369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35771225045930176022849825 26828418784447632017137369)
                ·
                  refine ⟨20121314088335724012853027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26828418784447632017137369 20121314088335724012853027)
                  ·
                    refine ⟨30181971132503586019279541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20121314088335724012853027 30181971132503586019279541)
                    ·
                      refine ⟨2829559793672211189307457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30181971132503586019279541 2829559793672211189307457)
                      ·
                        rfl

theorem cell23_5510548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_5510548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510548 prefixEnd_5510548 := by exact prefixLift 5510548
  have htrace : WordTrace (prefixWord ++ tailWord_5510548) baseStart_5510548 baseEnd_5510548 := by
    simpa [prefixWord, tailWord_5510548, baseEnd_5510548] using wordTrace_append hprefix tailTrace_5510548
  have hstable : (prefixWord ++ tailWord_5510548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510548).length < 2 ^ (prefixWord ++ tailWord_5510548).sum := by decide
  have hdescent : baseEnd_5510548 < baseStart_5510548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510585 : List Nat := [1, 2, 1, 4, 4, 1, 1, 4, 5]
def baseStart_5510585 : Nat := 118140960795 + 5510585 * 2 ^ 59
def prefixEnd_5510585 : Nat := 4983230072969 + 3 ^ 40 * 5510585 * 2
def baseEnd_5510585 : Nat := 314397643606269727171643

theorem tailTrace_5510585 : CollatzResearch.WordTrace tailWord_5510585 prefixEnd_5510585 314397643606269727171643 := by
  unfold tailWord_5510585
  simp only [CollatzResearch.WordTrace]
  refine ⟨200987546741099152835685209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133991697827399435223790139 200987546741099152835685209)
  ·
    refine ⟨150740660055824364626763907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200987546741099152835685209 150740660055824364626763907)
    ·
      refine ⟨226110990083736546940145861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150740660055824364626763907 226110990083736546940145861)
      ·
        refine ⟨42395810640700602551277349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226110990083736546940145861 42395810640700602551277349)
        ·
          refine ⟨7949214495131362978364503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42395810640700602551277349 7949214495131362978364503)
          ·
            refine ⟨11923821742697044467546755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7949214495131362978364503 11923821742697044467546755)
            ·
              refine ⟨17885732614045566701320133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11923821742697044467546755 17885732614045566701320133)
              ·
                refine ⟨3353574865133543756497525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17885732614045566701320133 3353574865133543756497525)
                ·
                  refine ⟨314397643606269727171643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3353574865133543756497525 314397643606269727171643)
                  ·
                    rfl

theorem cell23_5510585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 5].length) (baseStart_5510585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510585 prefixEnd_5510585 := by exact prefixLift 5510585
  have htrace : WordTrace (prefixWord ++ tailWord_5510585) baseStart_5510585 baseEnd_5510585 := by
    simpa [prefixWord, tailWord_5510585, baseEnd_5510585] using wordTrace_append hprefix tailTrace_5510585
  have hstable : (prefixWord ++ tailWord_5510585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510585).length < 2 ^ (prefixWord ++ tailWord_5510585).sum := by decide
  have hdescent : baseEnd_5510585 < baseStart_5510585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510601 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_5510601 : Nat := 118140960795 + 5510601 * 2 ^ 59
def prefixEnd_5510601 : Nat := 4983230072969 + 3 ^ 40 * 5510601 * 2
def baseEnd_5510601 : Nat := 2829587008146899481944713

theorem tailTrace_5510601 : CollatzResearch.WordTrace tailWord_5510601 prefixEnd_5510601 2829587008146899481944713 := by
  unfold tailWord_5510601
  simp only [CollatzResearch.WordTrace]
  refine ⟨200988130309041187568267657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133992086872694125045511771 200988130309041187568267657)
  ·
    refine ⟨150741097731780890676200743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200988130309041187568267657 150741097731780890676200743)
    ·
      refine ⟨226111646597671336014301115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150741097731780890676200743 226111646597671336014301115)
      ·
        refine ⟨339167469896507004021451673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226111646597671336014301115 339167469896507004021451673)
        ·
          refine ⟨254375602422380253016088755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339167469896507004021451673 254375602422380253016088755)
          ·
            refine ⟨381563403633570379524133133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254375602422380253016088755 381563403633570379524133133)
            ·
              refine ⟨143086276362588892321549925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381563403633570379524133133 143086276362588892321549925)
              ·
                refine ⟨26828676817985417310290611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143086276362588892321549925 26828676817985417310290611)
                ·
                  refine ⟨40243015226978125965435917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26828676817985417310290611 40243015226978125965435917)
                  ·
                    refine ⟨15091130710116797237038469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40243015226978125965435917 15091130710116797237038469)
                    ·
                      refine ⟨2829587008146899481944713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15091130710116797237038469 2829587008146899481944713)
                      ·
                        rfl

theorem cell23_5510601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_5510601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510601 prefixEnd_5510601 := by exact prefixLift 5510601
  have htrace : WordTrace (prefixWord ++ tailWord_5510601) baseStart_5510601 baseEnd_5510601 := by
    simpa [prefixWord, tailWord_5510601, baseEnd_5510601] using wordTrace_append hprefix tailTrace_5510601
  have hstable : (prefixWord ++ tailWord_5510601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510601).length < 2 ^ (prefixWord ++ tailWord_5510601).sum := by decide
  have hdescent : baseEnd_5510601 < baseStart_5510601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510618 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_5510618 : Nat := 118140960795 + 5510618 * 2 ^ 59
def prefixEnd_5510618 : Nat := 4983230072969 + 3 ^ 40 * 5510618 * 2
def baseEnd_5510618 : Nat := 2829595737318025915432135

theorem tailTrace_5510618 : CollatzResearch.WordTrace tailWord_5510618 prefixEnd_5510618 2829595737318025915432135 := by
  unfold tailWord_5510618
  simp only [CollatzResearch.WordTrace]
  refine ⟨50247187587494899867909127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133992500233319732981091005 50247187587494899867909127)
  ·
    refine ⟨75370781381242349801863691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50247187587494899867909127 75370781381242349801863691)
    ·
      refine ⟨113056172071863524702795537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75370781381242349801863691 113056172071863524702795537)
      ·
        refine ⟨84792129053897643527096653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113056172071863524702795537 84792129053897643527096653)
        ·
          refine ⟨31797048395211616322661245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84792129053897643527096653 31797048395211616322661245)
          ·
            refine ⟨11923893148204356120997967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31797048395211616322661245 11923893148204356120997967)
            ·
              refine ⟨17885839722306534181496951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11923893148204356120997967 17885839722306534181496951)
              ·
                refine ⟨26828759583459801272245427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17885839722306534181496951 26828759583459801272245427)
                ·
                  refine ⟨40243139375189701908368141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26828759583459801272245427 40243139375189701908368141)
                  ·
                    refine ⟨15091177265696138215638053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40243139375189701908368141 15091177265696138215638053)
                    ·
                      refine ⟨2829595737318025915432135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15091177265696138215638053 2829595737318025915432135)
                      ·
                        rfl

theorem cell23_5510618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_5510618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510618 prefixEnd_5510618 := by exact prefixLift 5510618
  have htrace : WordTrace (prefixWord ++ tailWord_5510618) baseStart_5510618 baseEnd_5510618 := by
    simpa [prefixWord, tailWord_5510618, baseEnd_5510618] using wordTrace_append hprefix tailTrace_5510618
  have hstable : (prefixWord ++ tailWord_5510618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510618).length < 2 ^ (prefixWord ++ tailWord_5510618).sum := by decide
  have hdescent : baseEnd_5510618 < baseStart_5510618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510661 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_5510661 : Nat := 118140960795 + 5510661 * 2 ^ 59
def prefixEnd_5510661 : Nat := 4983230072969 + 3 ^ 40 * 5510661 * 2
def baseEnd_5510661 : Nat := 2829617816986169247194437

theorem tailTrace_5510661 : CollatzResearch.WordTrace tailWord_5510661 prefixEnd_5510661 2829617816986169247194437 := by
  unfold tailWord_5510661
  simp only [CollatzResearch.WordTrace]
  refine ⟨200990318688823817815451837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133993545792549211876967891 200990318688823817815451837)
  ·
    refine ⟨75371369508308931680794439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200990318688823817815451837 75371369508308931680794439)
    ·
      refine ⟨113057054262463397521191659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75371369508308931680794439 113057054262463397521191659)
      ·
        refine ⟨169585581393695096281787489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113057054262463397521191659 169585581393695096281787489)
        ·
          refine ⟨127189186045271322211340617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169585581393695096281787489 127189186045271322211340617)
          ·
            refine ⟨95391889533953491658505463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127189186045271322211340617 95391889533953491658505463)
            ·
              refine ⟨143087834300930237487758195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95391889533953491658505463 143087834300930237487758195)
              ·
                refine ⟨214631751451395356231637293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143087834300930237487758195 214631751451395356231637293)
                ·
                  refine ⟨80486906794273258586863985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214631751451395356231637293 80486906794273258586863985)
                  ·
                    refine ⟨60365180095704943940147989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80486906794273258586863985 60365180095704943940147989)
                    ·
                      refine ⟨2829617816986169247194437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60365180095704943940147989 2829617816986169247194437)
                      ·
                        rfl

theorem cell23_5510661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_5510661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510661 prefixEnd_5510661 := by exact prefixLift 5510661
  have htrace : WordTrace (prefixWord ++ tailWord_5510661) baseStart_5510661 baseEnd_5510661 := by
    simpa [prefixWord, tailWord_5510661, baseEnd_5510661] using wordTrace_append hprefix tailTrace_5510661
  have hstable : (prefixWord ++ tailWord_5510661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510661).length < 2 ^ (prefixWord ++ tailWord_5510661).sum := by decide
  have hdescent : baseEnd_5510661 < baseStart_5510661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510681 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_5510681 : Nat := 118140960795 + 5510681 * 2 ^ 59
def prefixEnd_5510681 : Nat := 4983230072969 + 3 ^ 40 * 5510681 * 2
def baseEnd_5510681 : Nat := 2829628086599259168944345

theorem tailTrace_5510681 : CollatzResearch.WordTrace tailWord_5510681 prefixEnd_5510681 2829628086599259168944345 := by
  unfold tailWord_5510681
  simp only [CollatzResearch.WordTrace]
  refine ⟨200991048148751361231179897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133994032099167574154119931 200991048148751361231179897)
  ·
    refine ⟨150743286111563520923384923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200991048148751361231179897 150743286111563520923384923)
    ·
      refine ⟨226114929167345281385077385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150743286111563520923384923 226114929167345281385077385)
      ·
        refine ⟨169586196875508961038808039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226114929167345281385077385 169586196875508961038808039)
        ·
          refine ⟨254379295313263441558212059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169586196875508961038808039 254379295313263441558212059)
          ·
            refine ⟨381568942969895162337318089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254379295313263441558212059 381568942969895162337318089)
            ·
              refine ⟨286176707227421371752988567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381568942969895162337318089 286176707227421371752988567)
              ·
                refine ⟨429265060841132057629482851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286176707227421371752988567 429265060841132057629482851)
                ·
                  refine ⟨643897591261698086444224277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429265060841132057629482851 643897591261698086444224277)
                  ·
                    refine ⟨30182699590392097802073013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 643897591261698086444224277 30182699590392097802073013)
                    ·
                      refine ⟨2829628086599259168944345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30182699590392097802073013 2829628086599259168944345)
                      ·
                        rfl

theorem cell23_5510681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_5510681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510681 prefixEnd_5510681 := by exact prefixLift 5510681
  have htrace : WordTrace (prefixWord ++ tailWord_5510681) baseStart_5510681 baseEnd_5510681 := by
    simpa [prefixWord, tailWord_5510681, baseEnd_5510681] using wordTrace_append hprefix tailTrace_5510681
  have hstable : (prefixWord ++ tailWord_5510681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510681).length < 2 ^ (prefixWord ++ tailWord_5510681).sum := by decide
  have hdescent : baseEnd_5510681 < baseStart_5510681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510686 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5510686 : Nat := 118140960795 + 5510686 * 2 ^ 59
def prefixEnd_5510686 : Nat := 4983230072969 + 3 ^ 40 * 5510686 * 2
def baseEnd_5510686 : Nat := 2829630654002531649381823

theorem tailTrace_5510686 : CollatzResearch.WordTrace tailWord_5510686 prefixEnd_5510686 2829630654002531649381823 := by
  unfold tailWord_5510686
  simp only [CollatzResearch.WordTrace]
  refine ⟨25123903814216655885638989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133994153675822164723407941 25123903814216655885638989)
  ·
    refine ⟨9421463930331245957114621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25123903814216655885638989 9421463930331245957114621)
    ·
      refine ⟨3533048973874217233917983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9421463930331245957114621 3533048973874217233917983)
      ·
        refine ⟨5299573460811325850876975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533048973874217233917983 5299573460811325850876975)
        ·
          refine ⟨7949360191216988776315463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299573460811325850876975 7949360191216988776315463)
          ·
            refine ⟨11924040286825483164473195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7949360191216988776315463 11924040286825483164473195)
            ·
              refine ⟨17886060430238224746709793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11924040286825483164473195 17886060430238224746709793)
              ·
                refine ⟨13414545322678668560032345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17886060430238224746709793 13414545322678668560032345)
                ·
                  refine ⟨10060908992009001420024259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13414545322678668560032345 10060908992009001420024259)
                  ·
                    refine ⟨15091363488013502130036389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10060908992009001420024259 15091363488013502130036389)
                    ·
                      refine ⟨2829630654002531649381823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15091363488013502130036389 2829630654002531649381823)
                      ·
                        rfl

theorem cell23_5510686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5510686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510686 prefixEnd_5510686 := by exact prefixLift 5510686
  have htrace : WordTrace (prefixWord ++ tailWord_5510686) baseStart_5510686 baseEnd_5510686 := by
    simpa [prefixWord, tailWord_5510686, baseEnd_5510686] using wordTrace_append hprefix tailTrace_5510686
  have hstable : (prefixWord ++ tailWord_5510686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510686).length < 2 ^ (prefixWord ++ tailWord_5510686).sum := by decide
  have hdescent : baseEnd_5510686 < baseStart_5510686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510696 : List Nat := [2, 1, 5, 2, 2, 1, 3, 2, 1, 4]
def baseStart_5510696 : Nat := 118140960795 + 5510696 * 2 ^ 59
def prefixEnd_5510696 : Nat := 4983230072969 + 3 ^ 40 * 5510696 * 2
def baseEnd_5510696 : Nat := 943211929603025536752259

theorem tailTrace_5510696 : CollatzResearch.WordTrace tailWord_5510696 prefixEnd_5510696 943211929603025536752259 := by
  unfold tailWord_5510696
  simp only [CollatzResearch.WordTrace]
  refine ⟨100495797621848509396487971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133994396829131345861983961 100495797621848509396487971)
  ·
    refine ⟨150743696432772764094731957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100495797621848509396487971 150743696432772764094731957)
    ·
      refine ⟨14132221540572446633881121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150743696432772764094731957 14132221540572446633881121)
      ·
        refine ⟨10599166155429334975410841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14132221540572446633881121 10599166155429334975410841)
        ·
          refine ⟨7949374616572001231558131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10599166155429334975410841 7949374616572001231558131)
          ·
            refine ⟨11924061924858001847337197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7949374616572001231558131 11924061924858001847337197)
            ·
              refine ⟨4471523221821750692751449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11924061924858001847337197 4471523221821750692751449)
              ·
                refine ⟨3353642416366313019563587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4471523221821750692751449 3353642416366313019563587)
                ·
                  refine ⟨5030463624549469529345381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353642416366313019563587 5030463624549469529345381)
                  ·
                    refine ⟨943211929603025536752259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5030463624549469529345381 943211929603025536752259)
                    ·
                      rfl

theorem cell23_5510696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_5510696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510696 prefixEnd_5510696 := by exact prefixLift 5510696
  have htrace : WordTrace (prefixWord ++ tailWord_5510696) baseStart_5510696 baseEnd_5510696 := by
    simpa [prefixWord, tailWord_5510696, baseEnd_5510696] using wordTrace_append hprefix tailTrace_5510696
  have hstable : (prefixWord ++ tailWord_5510696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510696).length < 2 ^ (prefixWord ++ tailWord_5510696).sum := by decide
  have hdescent : baseEnd_5510696 < baseStart_5510696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510745 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 3]
def baseStart_5510745 : Nat := 118140960795 + 5510745 * 2 ^ 59
def prefixEnd_5510745 : Nat := 4983230072969 + 3 ^ 40 * 5510745 * 2
def baseEnd_5510745 : Nat := 2829660949361146918544051

theorem tailTrace_5510745 : CollatzResearch.WordTrace tailWord_5510745 prefixEnd_5510745 2829660949361146918544051 := by
  unfold tailWord_5510745
  simp only [CollatzResearch.WordTrace]
  refine ⟨200993382420519500161509689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133995588280346333441006459 200993382420519500161509689)
  ·
    refine ⟨150745036815389625121132267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200993382420519500161509689 150745036815389625121132267)
    ·
      refine ⟨226117555223084437681698401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150745036815389625121132267 226117555223084437681698401)
      ·
        refine ⟨169588166417313328261273801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226117555223084437681698401 169588166417313328261273801)
        ·
          refine ⟨127191124812984996195955351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169588166417313328261273801 127191124812984996195955351)
          ·
            refine ⟨190786687219477494293933027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127191124812984996195955351 190786687219477494293933027)
            ·
              refine ⟨286180030829216241440899541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190786687219477494293933027 286180030829216241440899541)
              ·
                refine ⟨6707344472559755658771083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 286180030829216241440899541 6707344472559755658771083)
                ·
                  refine ⟨10061016708839633488156625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6707344472559755658771083 10061016708839633488156625)
                  ·
                    refine ⟨7545762531629725116117469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10061016708839633488156625 7545762531629725116117469)
                    ·
                      refine ⟨2829660949361146918544051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7545762531629725116117469 2829660949361146918544051)
                      ·
                        rfl

theorem cell23_5510745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_5510745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510745 prefixEnd_5510745 := by exact prefixLift 5510745
  have htrace : WordTrace (prefixWord ++ tailWord_5510745) baseStart_5510745 baseEnd_5510745 := by
    simpa [prefixWord, tailWord_5510745, baseEnd_5510745] using wordTrace_append hprefix tailTrace_5510745
  have hstable : (prefixWord ++ tailWord_5510745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510745).length < 2 ^ (prefixWord ++ tailWord_5510745).sum := by decide
  have hdescent : baseEnd_5510745 < baseStart_5510745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510748 : List Nat := [2, 2, 4, 1, 2, 12]
def baseStart_5510748 : Nat := 118140960795 + 5510748 * 2 ^ 59
def prefixEnd_5510748 : Nat := 4983230072969 + 3 ^ 40 * 5510748 * 2
def baseEnd_5510748 : Nat := 11644701604128026365459

theorem tailTrace_5510748 : CollatzResearch.WordTrace tailWord_5510748 prefixEnd_5510748 11644701604128026365459 := by
  unfold tailWord_5510748
  simp only [CollatzResearch.WordTrace]
  refine ⟨100496745919754315836934449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133995661226339087782579265 100496745919754315836934449)
  ·
    refine ⟨75372559439815736877700837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100496745919754315836934449 75372559439815736877700837)
    ·
      refine ⟨14132354894965450664568907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75372559439815736877700837 14132354894965450664568907)
      ·
        refine ⟨21198532342448175996853361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14132354894965450664568907 21198532342448175996853361)
        ·
          refine ⟨15898899256836131997640021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21198532342448175996853361 15898899256836131997640021)
          ·
            refine ⟨11644701604128026365459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15898899256836131997640021 11644701604128026365459)
            ·
              rfl

theorem cell23_5510748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 12].length) (baseStart_5510748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510748 prefixEnd_5510748 := by exact prefixLift 5510748
  have htrace : WordTrace (prefixWord ++ tailWord_5510748) baseStart_5510748 baseEnd_5510748 := by
    simpa [prefixWord, tailWord_5510748, baseEnd_5510748] using wordTrace_append hprefix tailTrace_5510748
  have hstable : (prefixWord ++ tailWord_5510748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510748).length < 2 ^ (prefixWord ++ tailWord_5510748).sum := by decide
  have hdescent : baseEnd_5510748 < baseStart_5510748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510775 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_5510775 : Nat := 118140960795 + 5510775 * 2 ^ 59
def prefixEnd_5510775 : Nat := 4983230072969 + 3 ^ 40 * 5510775 * 2
def baseEnd_5510775 : Nat := 2829676353780781801168913

theorem tailTrace_5510775 : CollatzResearch.WordTrace tailWord_5510775 prefixEnd_5510775 2829676353780781801168913 := by
  unfold tailWord_5510775
  simp only [CollatzResearch.WordTrace]
  refine ⟨200994476610410815285101779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133996317740273876856734519 200994476610410815285101779)
  ·
    refine ⟨301491714915616222927652669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200994476610410815285101779 301491714915616222927652669)
    ·
      refine ⟨113059393093356083597869751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301491714915616222927652669 113059393093356083597869751)
      ·
        refine ⟨169589089640034125396804627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113059393093356083597869751 169589089640034125396804627)
        ·
          refine ⟨254383634460051188095206941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169589089640034125396804627 254383634460051188095206941)
          ·
            refine ⟨95393862922519195535702603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254383634460051188095206941 95393862922519195535702603)
            ·
              refine ⟨143090794383778793303553905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95393862922519195535702603 143090794383778793303553905)
              ·
                refine ⟨107318095787834094977665429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143090794383778793303553905 107318095787834094977665429)
                ·
                  refine ⟨5030535740054723202078067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107318095787834094977665429 5030535740054723202078067)
                  ·
                    refine ⟨7545803610082084803117101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5030535740054723202078067 7545803610082084803117101)
                    ·
                      refine ⟨2829676353780781801168913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7545803610082084803117101 2829676353780781801168913)
                      ·
                        rfl

theorem cell23_5510775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_5510775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510775 prefixEnd_5510775 := by exact prefixLift 5510775
  have htrace : WordTrace (prefixWord ++ tailWord_5510775) baseStart_5510775 baseEnd_5510775 := by
    simpa [prefixWord, tailWord_5510775, baseEnd_5510775] using wordTrace_append hprefix tailTrace_5510775
  have hstable : (prefixWord ++ tailWord_5510775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510775).length < 2 ^ (prefixWord ++ tailWord_5510775).sum := by decide
  have hdescent : baseEnd_5510775 < baseStart_5510775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510832 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 1, 4, 2]
def baseStart_5510832 : Nat := 118140960795 + 5510832 * 2 ^ 59
def prefixEnd_5510832 : Nat := 4983230072969 + 3 ^ 40 * 5510832 * 2
def baseEnd_5510832 : Nat := 2829705622178088078156151

theorem tailTrace_5510832 : CollatzResearch.WordTrace tailWord_5510832 prefixEnd_5510832 2829705622178088078156151 := by
  unfold tailWord_5510832
  simp only [CollatzResearch.WordTrace]
  refine ⟨100498277785602157009963375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133997703714136209346617833 100498277785602157009963375)
  ·
    refine ⟨150747416678403235514945063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100498277785602157009963375 150747416678403235514945063)
    ·
      refine ⟨226121125017604853272417595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150747416678403235514945063 226121125017604853272417595)
      ·
        refine ⟨339181687526407279908626393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226121125017604853272417595 339181687526407279908626393)
        ·
          refine ⟨254386265644805459931469795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339181687526407279908626393 254386265644805459931469795)
          ·
            refine ⟨381579398467208189897204693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254386265644805459931469795 381579398467208189897204693)
            ·
              refine ⟨8943267151575191950715735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 381579398467208189897204693 8943267151575191950715735)
              ·
                refine ⟨13414900727362787926073603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8943267151575191950715735 13414900727362787926073603)
                ·
                  refine ⟨20122351091044181889110405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13414900727362787926073603 20122351091044181889110405)
                  ·
                    refine ⟨3772940829570784104208201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20122351091044181889110405 3772940829570784104208201)
                    ·
                      refine ⟨2829705622178088078156151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772940829570784104208201 2829705622178088078156151)
                      ·
                        rfl

theorem cell23_5510832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 4, 2].length) (baseStart_5510832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510832 prefixEnd_5510832 := by exact prefixLift 5510832
  have htrace : WordTrace (prefixWord ++ tailWord_5510832) baseStart_5510832 baseEnd_5510832 := by
    simpa [prefixWord, tailWord_5510832, baseEnd_5510832] using wordTrace_append hprefix tailTrace_5510832
  have hstable : (prefixWord ++ tailWord_5510832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510832).length < 2 ^ (prefixWord ++ tailWord_5510832).sum := by decide
  have hdescent : baseEnd_5510832 < baseStart_5510832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510885 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_5510885 : Nat := 118140960795 + 5510885 * 2 ^ 59
def prefixEnd_5510885 : Nat := 4983230072969 + 3 ^ 40 * 5510885 * 2
def baseEnd_5510885 : Nat := 943244278884258790264469

theorem tailTrace_5510885 : CollatzResearch.WordTrace tailWord_5510885 prefixEnd_5510885 943244278884258790264469 := by
  unfold tailWord_5510885
  simp only [CollatzResearch.WordTrace]
  refine ⟨200998488640012304071606109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133998992426674869381070739 200998488640012304071606109)
  ·
    refine ⟨75374433240004614026852291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200998488640012304071606109 75374433240004614026852291)
    ·
      refine ⟨113061649860006921040278437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75374433240004614026852291 113061649860006921040278437)
      ·
        refine ⟨21199059348751297695052207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113061649860006921040278437 21199059348751297695052207)
        ·
          refine ⟨31798589023126946542578311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21199059348751297695052207 31798589023126946542578311)
          ·
            refine ⟨47697883534690419813867467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31798589023126946542578311 47697883534690419813867467)
            ·
              refine ⟨71546825302035629720801201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47697883534690419813867467 71546825302035629720801201)
              ·
                refine ⟨53660118976526722290600901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71546825302035629720801201 53660118976526722290600901)
                ·
                  refine ⟨10061272308098760429487669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53660118976526722290600901 10061272308098760429487669)
                  ·
                    refine ⟨943244278884258790264469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10061272308098760429487669 943244278884258790264469)
                    ·
                      rfl

theorem cell23_5510885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_5510885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510885 prefixEnd_5510885 := by exact prefixLift 5510885
  have htrace : WordTrace (prefixWord ++ tailWord_5510885) baseStart_5510885 baseEnd_5510885 := by
    simpa [prefixWord, tailWord_5510885, baseEnd_5510885] using wordTrace_append hprefix tailTrace_5510885
  have hstable : (prefixWord ++ tailWord_5510885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510885).length < 2 ^ (prefixWord ++ tailWord_5510885).sum := by decide
  have hdescent : baseEnd_5510885 < baseStart_5510885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510902 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_5510902 : Nat := 118140960795 + 5510902 * 2 ^ 59
def prefixEnd_5510902 : Nat := 4983230072969 + 3 ^ 40 * 5510902 * 2
def baseEnd_5510902 : Nat := 943247188607967601426943

theorem tailTrace_5510902 : CollatzResearch.WordTrace tailWord_5510902 prefixEnd_5510902 943247188607967601426943 := by
  unfold tailWord_5510902
  simp only [CollatzResearch.WordTrace]
  refine ⟨12562444292559419748435935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133999405787300477316649973 12562444292559419748435935)
  ·
    refine ⟨18843666438839129622653903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12562444292559419748435935 18843666438839129622653903)
    ·
      refine ⟨28265499658258694433980855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18843666438839129622653903 28265499658258694433980855)
      ·
        refine ⟨42398249487388041650971283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28265499658258694433980855 42398249487388041650971283)
        ·
          refine ⟨63597374231082062476456925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42398249487388041650971283 63597374231082062476456925)
          ·
            refine ⟨23849015336655773428671347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63597374231082062476456925 23849015336655773428671347)
            ·
              refine ⟨35773523004983660143007021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23849015336655773428671347 35773523004983660143007021)
              ·
                refine ⟨13415071126868872553627633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35773523004983660143007021 13415071126868872553627633)
                ·
                  refine ⟨10061303345151654415220725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13415071126868872553627633 10061303345151654415220725)
                  ·
                    refine ⟨943247188607967601426943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10061303345151654415220725 943247188607967601426943)
                    ·
                      rfl

theorem cell23_5510902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_5510902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510902 prefixEnd_5510902 := by exact prefixLift 5510902
  have htrace : WordTrace (prefixWord ++ tailWord_5510902) baseStart_5510902 baseEnd_5510902 := by
    simpa [prefixWord, tailWord_5510902, baseEnd_5510902] using wordTrace_append hprefix tailTrace_5510902
  have hstable : (prefixWord ++ tailWord_5510902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510902).length < 2 ^ (prefixWord ++ tailWord_5510902).sum := by decide
  have hdescent : baseEnd_5510902 < baseStart_5510902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5510922 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_5510922 : Nat := 118140960795 + 5510922 * 2 ^ 59
def prefixEnd_5510922 : Nat := 4983230072969 + 3 ^ 40 * 5510922 * 2
def baseEnd_5510922 : Nat := 2829751835436992726030737

theorem tailTrace_5510922 : CollatzResearch.WordTrace tailWord_5510922 prefixEnd_5510922 2829751835436992726030737 := by
  unfold tailWord_5510922
  simp only [CollatzResearch.WordTrace]
  refine ⟨50249959535219564847675755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133999892093918839593802013 50249959535219564847675755)
  ·
    refine ⟨75374939302829347271513633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50249959535219564847675755 75374939302829347271513633)
    ·
      refine ⟨56531204477122010453635225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75374939302829347271513633 56531204477122010453635225)
      ·
        refine ⟨42398403357841507840226419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56531204477122010453635225 42398403357841507840226419)
        ·
          refine ⟨63597605036762261760339629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42398403357841507840226419 63597605036762261760339629)
          ·
            refine ⟨23849101888785848160127361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63597605036762261760339629 23849101888785848160127361)
            ·
              refine ⟨17886826416589386120095521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23849101888785848160127361 17886826416589386120095521)
              ·
                refine ⟨13415119812442039590071641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17886826416589386120095521 13415119812442039590071641)
                ·
                  refine ⟨10061339859331529692553731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13415119812442039590071641 10061339859331529692553731)
                  ·
                    refine ⟨15092009788997294538830597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10061339859331529692553731 15092009788997294538830597)
                    ·
                      refine ⟨2829751835436992726030737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15092009788997294538830597 2829751835436992726030737)
                      ·
                        rfl

theorem cell23_5510922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_5510922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5510922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5510922 prefixEnd_5510922 := by exact prefixLift 5510922
  have htrace : WordTrace (prefixWord ++ tailWord_5510922) baseStart_5510922 baseEnd_5510922 := by
    simpa [prefixWord, tailWord_5510922, baseEnd_5510922] using wordTrace_append hprefix tailTrace_5510922
  have hstable : (prefixWord ++ tailWord_5510922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5510922).length < 2 ^ (prefixWord ++ tailWord_5510922).sum := by decide
  have hdescent : baseEnd_5510922 < baseStart_5510922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5510922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511029 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_5511029 : Nat := 118140960795 + 5511029 * 2 ^ 59
def prefixEnd_5511029 : Nat := 4983230072969 + 3 ^ 40 * 5511029 * 2
def baseEnd_5511029 : Nat := 2829806777867023807392745

theorem tailTrace_5511029 : CollatzResearch.WordTrace tailWord_5511029 prefixEnd_5511029 2829806777867023807392745 := by
  unfold tailWord_5511029
  simp only [CollatzResearch.WordTrace]
  refine ⟨201003740751490616664848141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134002493834327077776565427 201003740751490616664848141)
  ·
    refine ⟨75376402781808981249318053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201003740751490616664848141 75376402781808981249318053)
    ·
      refine ⟨14133075521589183984247135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75376402781808981249318053 14133075521589183984247135)
      ·
        refine ⟨21199613282383775976370703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14133075521589183984247135 21199613282383775976370703)
        ·
          refine ⟨31799419923575663964556055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21199613282383775976370703 31799419923575663964556055)
          ·
            refine ⟨47699129885363495946834083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31799419923575663964556055 47699129885363495946834083)
            ·
              refine ⟨71548694828045243920251125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47699129885363495946834083 71548694828045243920251125)
              ·
                refine ⟨6707690140129241617523543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71548694828045243920251125 6707690140129241617523543)
                ·
                  refine ⟨10061535210193862426285315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6707690140129241617523543 10061535210193862426285315)
                  ·
                    refine ⟨15092302815290793639427973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10061535210193862426285315 15092302815290793639427973)
                    ·
                      refine ⟨2829806777867023807392745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15092302815290793639427973 2829806777867023807392745)
                      ·
                        rfl

theorem cell23_5511029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_5511029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511029 prefixEnd_5511029 := by exact prefixLift 5511029
  have htrace : WordTrace (prefixWord ++ tailWord_5511029) baseStart_5511029 baseEnd_5511029 := by
    simpa [prefixWord, tailWord_5511029, baseEnd_5511029] using wordTrace_append hprefix tailTrace_5511029
  have hstable : (prefixWord ++ tailWord_5511029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511029).length < 2 ^ (prefixWord ++ tailWord_5511029).sum := by decide
  have hdescent : baseEnd_5511029 < baseStart_5511029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511066 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_5511066 : Nat := 118140960795 + 5511066 * 2 ^ 59
def prefixEnd_5511066 : Nat := 4983230072969 + 3 ^ 40 * 5511066 * 2
def baseEnd_5511066 : Nat := 2829825776651240162630075

theorem tailTrace_5511066 : CollatzResearch.WordTrace tailWord_5511066 prefixEnd_5511066 2829825776651240162630075 := by
  unfold tailWord_5511066
  simp only [CollatzResearch.WordTrace]
  refine ⟨50251272563089142995986263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134003393501571047989296701 50251272563089142995986263)
  ·
    refine ⟨75376908844633714493979395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50251272563089142995986263 75376908844633714493979395)
    ·
      refine ⟨113065363266950571740969093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75376908844633714493979395 113065363266950571740969093)
      ·
        refine ⟨21199755612553232201431705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113065363266950571740969093 21199755612553232201431705)
        ·
          refine ⟨15899816709414924151073779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21199755612553232201431705 15899816709414924151073779)
          ·
            refine ⟨23849725064122386226610669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15899816709414924151073779 23849725064122386226610669)
            ·
              refine ⟨8943646899045894834979001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23849725064122386226610669 8943646899045894834979001)
              ·
                refine ⟨6707735174284421126234251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8943646899045894834979001 6707735174284421126234251)
                ·
                  refine ⟨10061602761426631689351377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6707735174284421126234251 10061602761426631689351377)
                  ·
                    refine ⟨7546202071069973767013533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10061602761426631689351377 7546202071069973767013533)
                    ·
                      refine ⟨2829825776651240162630075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546202071069973767013533 2829825776651240162630075)
                      ·
                        rfl

theorem cell23_5511066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_5511066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511066 prefixEnd_5511066 := by exact prefixLift 5511066
  have htrace : WordTrace (prefixWord ++ tailWord_5511066) baseStart_5511066 baseEnd_5511066 := by
    simpa [prefixWord, tailWord_5511066, baseEnd_5511066] using wordTrace_append hprefix tailTrace_5511066
  have hstable : (prefixWord ++ tailWord_5511066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511066).length < 2 ^ (prefixWord ++ tailWord_5511066).sum := by decide
  have hdescent : baseEnd_5511066 < baseStart_5511066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511079 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_5511079 : Nat := 118140960795 + 5511079 * 2 ^ 59
def prefixEnd_5511079 : Nat := 4983230072969 + 3 ^ 40 * 5511079 * 2
def baseEnd_5511079 : Nat := 2829832451899748611767515

theorem tailTrace_5511079 : CollatzResearch.WordTrace tailWord_5511079 prefixEnd_5511079 2829832451899748611767515 := by
  unfold tailWord_5511079
  simp only [CollatzResearch.WordTrace]
  refine ⟨201005564401309475204168291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134003709600872983469445527 201005564401309475204168291)
  ·
    refine ⟨301508346601964212806252437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201005564401309475204168291 301508346601964212806252437)
    ·
      refine ⟨14133203746967072475293083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 301508346601964212806252437 14133203746967072475293083)
      ·
        refine ⟨21199805620450608712939625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14133203746967072475293083 21199805620450608712939625)
        ·
          refine ⟨15899854215337956534704719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21199805620450608712939625 15899854215337956534704719)
          ·
            refine ⟨23849781323006934802057079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15899854215337956534704719 23849781323006934802057079)
            ·
              refine ⟨35774671984510402203085619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23849781323006934802057079 35774671984510402203085619)
              ·
                refine ⟨53662007976765603304628429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35774671984510402203085619 53662007976765603304628429)
                ·
                  refine ⟨20123252991287101239235661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53662007976765603304628429 20123252991287101239235661)
                  ·
                    refine ⟨7546219871732662964713373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20123252991287101239235661 7546219871732662964713373)
                    ·
                      refine ⟨2829832451899748611767515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546219871732662964713373 2829832451899748611767515)
                      ·
                        rfl

theorem cell23_5511079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_5511079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511079 prefixEnd_5511079 := by exact prefixLift 5511079
  have htrace : WordTrace (prefixWord ++ tailWord_5511079) baseStart_5511079 baseEnd_5511079 := by
    simpa [prefixWord, tailWord_5511079, baseEnd_5511079] using wordTrace_append hprefix tailTrace_5511079
  have hstable : (prefixWord ++ tailWord_5511079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511079).length < 2 ^ (prefixWord ++ tailWord_5511079).sum := by decide
  have hdescent : baseEnd_5511079 < baseStart_5511079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511080 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5511080 : Nat := 118140960795 + 5511080 * 2 ^ 59
def prefixEnd_5511080 : Nat := 4983230072969 + 3 ^ 40 * 5511080 * 2
def baseEnd_5511080 : Nat := 2829832965380403107855011

theorem tailTrace_5511080 : CollatzResearch.WordTrace tailWord_5511080 prefixEnd_5511080 2829832965380403107855011 := by
  unfold tailWord_5511080
  simp only [CollatzResearch.WordTrace]
  refine ⟨100502800437152926187477347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134003733916203901583303129 100502800437152926187477347)
  ·
    refine ⟨150754200655729389281216021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100502800437152926187477347 150754200655729389281216021)
    ·
      refine ⟨7066603155737315122557001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150754200655729389281216021 7066603155737315122557001)
      ·
        refine ⟨5299952366802986341917751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7066603155737315122557001 5299952366802986341917751)
        ·
          refine ⟨7949928550204479512876627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299952366802986341917751 7949928550204479512876627)
          ·
            refine ⟨11924892825306719269314941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7949928550204479512876627 11924892825306719269314941)
            ·
              refine ⟨4471834809490019725993103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11924892825306719269314941 4471834809490019725993103)
              ·
                refine ⟨6707752214235029588989655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4471834809490019725993103 6707752214235029588989655)
                ·
                  refine ⟨10061628321352544383484483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6707752214235029588989655 10061628321352544383484483)
                  ·
                    refine ⟨15092442482028816575226725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10061628321352544383484483 15092442482028816575226725)
                    ·
                      refine ⟨2829832965380403107855011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15092442482028816575226725 2829832965380403107855011)
                      ·
                        rfl

theorem cell23_5511080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5511080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511080 prefixEnd_5511080 := by exact prefixLift 5511080
  have htrace : WordTrace (prefixWord ++ tailWord_5511080) baseStart_5511080 baseEnd_5511080 := by
    simpa [prefixWord, tailWord_5511080, baseEnd_5511080] using wordTrace_append hprefix tailTrace_5511080
  have hstable : (prefixWord ++ tailWord_5511080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511080).length < 2 ^ (prefixWord ++ tailWord_5511080).sum := by decide
  have hdescent : baseEnd_5511080 < baseStart_5511080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511086 : List Nat := [4, 1, 5, 1, 1, 11]
def baseStart_5511086 : Nat := 118140960795 + 5511086 * 2 ^ 59
def prefixEnd_5511086 : Nat := 4983230072969 + 3 ^ 40 * 5511086 * 2
def baseEnd_5511086 : Nat := 11645415828248271952181

theorem tailTrace_5511086 : CollatzResearch.WordTrace tailWord_5511086 prefixEnd_5511086 11645415828248271952181 := by
  unfold tailWord_5511086
  simp only [CollatzResearch.WordTrace]
  refine ⟨25125727464035514424959139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134003879808189410266448741 25125727464035514424959139)
  ·
    refine ⟨37688591196053271637438709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25125727464035514424959139 37688591196053271637438709)
    ·
      refine ⟨3533305424629994216009879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37688591196053271637438709 3533305424629994216009879)
      ·
        refine ⟨5299958136944991324014819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533305424629994216009879 5299958136944991324014819)
        ·
          refine ⟨7949937205417486986022229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299958136944991324014819 7949937205417486986022229)
          ·
            refine ⟨11645415828248271952181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7949937205417486986022229 11645415828248271952181)
            ·
              rfl

theorem cell23_5511086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 11].length) (baseStart_5511086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511086 prefixEnd_5511086 := by exact prefixLift 5511086
  have htrace : WordTrace (prefixWord ++ tailWord_5511086) baseStart_5511086 baseEnd_5511086 := by
    simpa [prefixWord, tailWord_5511086, baseEnd_5511086] using wordTrace_append hprefix tailTrace_5511086
  have hstable : (prefixWord ++ tailWord_5511086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511086).length < 2 ^ (prefixWord ++ tailWord_5511086).sum := by decide
  have hdescent : baseEnd_5511086 < baseStart_5511086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511096 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_5511096 : Nat := 118140960795 + 5511096 * 2 ^ 59
def prefixEnd_5511096 : Nat := 4983230072969 + 3 ^ 40 * 5511096 * 2
def baseEnd_5511096 : Nat := 2829841181070875045254937

theorem tailTrace_5511096 : CollatzResearch.WordTrace tailWord_5511096 prefixEnd_5511096 2829841181070875045254937 := by
  unfold tailWord_5511096
  simp only [CollatzResearch.WordTrace]
  refine ⟨100503092221123943553768571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134004122961498591405024761 100503092221123943553768571)
  ·
    refine ⟨150754638331685915330652857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100503092221123943553768571 150754638331685915330652857)
    ·
      refine ⟨113065978748764436497989643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150754638331685915330652857 113065978748764436497989643)
      ·
        refine ⟨169598968123146654746984465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113065978748764436497989643 169598968123146654746984465)
        ·
          refine ⟨127199226092359991060238349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169598968123146654746984465 127199226092359991060238349)
          ·
            refine ⟨47699709784634996647589381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127199226092359991060238349 47699709784634996647589381)
            ·
              refine ⟨8943695584619061871423009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47699709784634996647589381 8943695584619061871423009)
              ·
                refine ⟨6707771688464296403567257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8943695584619061871423009 6707771688464296403567257)
                ·
                  refine ⟨5030828766348222302675443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6707771688464296403567257 5030828766348222302675443)
                  ·
                    refine ⟨7546243149522333454013165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5030828766348222302675443 7546243149522333454013165)
                    ·
                      refine ⟨2829841181070875045254937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546243149522333454013165 2829841181070875045254937)
                      ·
                        rfl

theorem cell23_5511096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_5511096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511096 prefixEnd_5511096 := by exact prefixLift 5511096
  have htrace : WordTrace (prefixWord ++ tailWord_5511096) baseStart_5511096 baseEnd_5511096 := by
    simpa [prefixWord, tailWord_5511096, baseEnd_5511096] using wordTrace_append hprefix tailTrace_5511096
  have hstable : (prefixWord ++ tailWord_5511096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511096).length < 2 ^ (prefixWord ++ tailWord_5511096).sum := by decide
  have hdescent : baseEnd_5511096 < baseStart_5511096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511112 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 1, 8]
def baseStart_5511112 : Nat := 118140960795 + 5511112 * 2 ^ 59
def prefixEnd_5511112 : Nat := 4983230072969 + 3 ^ 40 * 5511112 * 2
def baseEnd_5511112 : Nat := 943283132253782327551621

theorem tailTrace_5511112 : CollatzResearch.WordTrace tailWord_5511112 prefixEnd_5511112 943283132253782327551621 := by
  unfold tailWord_5511112
  simp only [CollatzResearch.WordTrace]
  refine ⟨100503384005094960920059795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134004512006793281226746393 100503384005094960920059795)
  ·
    refine ⟨150755076007642441380089693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100503384005094960920059795 150755076007642441380089693)
    ·
      refine ⟨56533153502865915517533635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150755076007642441380089693 56533153502865915517533635)
      ·
        refine ⟨84799730254298873276300453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56533153502865915517533635 84799730254298873276300453)
        ·
          refine ⟨15899949422681038739306335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84799730254298873276300453 15899949422681038739306335)
          ·
            refine ⟨23849924134021558108959503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15899949422681038739306335 23849924134021558108959503)
            ·
              refine ⟨35774886201032337163439255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23849924134021558108959503 35774886201032337163439255)
              ·
                refine ⟨53662329301548505745158883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35774886201032337163439255 53662329301548505745158883)
                ·
                  refine ⟨80493493952322758617738325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53662329301548505745158883 80493493952322758617738325)
                  ·
                    refine ⟨943283132253782327551621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80493493952322758617738325 943283132253782327551621)
                    ·
                      rfl

theorem cell23_5511112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_5511112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511112 prefixEnd_5511112 := by exact prefixLift 5511112
  have htrace : WordTrace (prefixWord ++ tailWord_5511112) baseStart_5511112 baseEnd_5511112 := by
    simpa [prefixWord, tailWord_5511112, baseEnd_5511112] using wordTrace_append hprefix tailTrace_5511112
  have hstable : (prefixWord ++ tailWord_5511112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511112).length < 2 ^ (prefixWord ++ tailWord_5511112).sum := by decide
  have hdescent : baseEnd_5511112 < baseStart_5511112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511153 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 4, 2, 2]
def baseStart_5511153 : Nat := 118140960795 + 5511153 * 2 ^ 59
def prefixEnd_5511153 : Nat := 4983230072969 + 3 ^ 40 * 5511153 * 2
def baseEnd_5511153 : Nat := 2829870449468181322242175

theorem tailTrace_5511153 : CollatzResearch.WordTrace tailWord_5511153 prefixEnd_5511153 2829870449468181322242175 := by
  unfold tailWord_5511153
  simp only [CollatzResearch.WordTrace]
  refine ⟨201008263403041385842362113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134005508935360923894908075 201008263403041385842362113)
  ·
    refine ⟨150756197552281039381771585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201008263403041385842362113 150756197552281039381771585)
    ·
      refine ⟨113067148164210779536328689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150756197552281039381771585 113067148164210779536328689)
      ·
        refine ⟨84800361123158084652246517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113067148164210779536328689 84800361123158084652246517)
        ·
          refine ⟨7950033855296070436148111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84800361123158084652246517 7950033855296070436148111)
          ·
            refine ⟨11925050782944105654222167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950033855296070436148111 11925050782944105654222167)
            ·
              refine ⟨17887576174416158481333251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925050782944105654222167 17887576174416158481333251)
              ·
                refine ⟨26831364261624237721999877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17887576174416158481333251 26831364261624237721999877)
                ·
                  refine ⟨5030880799054544572874977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26831364261624237721999877 5030880799054544572874977)
                  ·
                    refine ⟨3773160599290908429656233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5030880799054544572874977 3773160599290908429656233)
                    ·
                      refine ⟨2829870449468181322242175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773160599290908429656233 2829870449468181322242175)
                      ·
                        rfl

theorem cell23_5511153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_5511153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511153 prefixEnd_5511153 := by exact prefixLift 5511153
  have htrace : WordTrace (prefixWord ++ tailWord_5511153) baseStart_5511153 baseEnd_5511153 := by
    simpa [prefixWord, tailWord_5511153, baseEnd_5511153] using wordTrace_append hprefix tailTrace_5511153
  have hstable : (prefixWord ++ tailWord_5511153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511153).length < 2 ^ (prefixWord ++ tailWord_5511153).sum := by decide
  have hdescent : baseEnd_5511153 < baseStart_5511153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511166 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5511166 : Nat := 118140960795 + 5511166 * 2 ^ 59
def prefixEnd_5511166 : Nat := 4983230072969 + 3 ^ 40 * 5511166 * 2
def baseEnd_5511166 : Nat := 2829877124716689771379615

theorem tailTrace_5511166 : CollatzResearch.WordTrace tailWord_5511166 prefixEnd_5511166 2829877124716689771379615 := by
  unfold tailWord_5511166
  simp only [CollatzResearch.WordTrace]
  refine ⟨25126092193999286132823169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134005825034662859375056901 25126092193999286132823169)
  ·
    refine ⟨18844569145499464599617377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25126092193999286132823169 18844569145499464599617377)
    ·
      refine ⟨14133426859124598449713033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18844569145499464599617377 14133426859124598449713033)
      ·
        refine ⟨10600070144343448837284775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14133426859124598449713033 10600070144343448837284775)
        ·
          refine ⟨15900105216515173255927163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10600070144343448837284775 15900105216515173255927163)
          ·
            refine ⟨23850157824772759883890745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15900105216515173255927163 23850157824772759883890745)
            ·
              refine ⟨17887618368579569912918059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23850157824772759883890745 17887618368579569912918059)
              ·
                refine ⟨26831427552869354869377089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17887618368579569912918059 26831427552869354869377089)
                ·
                  refine ⟨20123570664652016152032817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26831427552869354869377089 20123570664652016152032817)
                  ·
                    refine ⟨15092677998489012114024613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20123570664652016152032817 15092677998489012114024613)
                    ·
                      refine ⟨2829877124716689771379615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15092677998489012114024613 2829877124716689771379615)
                      ·
                        rfl

theorem cell23_5511166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5511166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511166 prefixEnd_5511166 := by exact prefixLift 5511166
  have htrace : WordTrace (prefixWord ++ tailWord_5511166) baseStart_5511166 baseEnd_5511166 := by
    simpa [prefixWord, tailWord_5511166, baseEnd_5511166] using wordTrace_append hprefix tailTrace_5511166
  have hstable : (prefixWord ++ tailWord_5511166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511166).length < 2 ^ (prefixWord ++ tailWord_5511166).sum := by decide
  have hdescent : baseEnd_5511166 < baseStart_5511166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511169 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_5511169 : Nat := 118140960795 + 5511169 * 2 ^ 59
def prefixEnd_5511169 : Nat := 4983230072969 + 3 ^ 40 * 5511169 * 2
def baseEnd_5511169 : Nat := 2829878665158653259642101

theorem tailTrace_5511169 : CollatzResearch.WordTrace tailWord_5511169 prefixEnd_5511169 2829878665158653259642101 := by
  unfold tailWord_5511169
  simp only [CollatzResearch.WordTrace]
  refine ⟨201008846970983420574944561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134005897980655613716629707 201008846970983420574944561)
  ·
    refine ⟨150756635228237565431208421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201008846970983420574944561 150756635228237565431208421)
    ·
      refine ⟨28266869105294543518351579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150756635228237565431208421 28266869105294543518351579)
      ·
        refine ⟨42400303657941815277527369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28266869105294543518351579 42400303657941815277527369)
        ·
          refine ⟨31800227743456361458145527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42400303657941815277527369 31800227743456361458145527)
          ·
            refine ⟨47700341615184542187218291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31800227743456361458145527 47700341615184542187218291)
            ·
              refine ⟨71550512422776813280827437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47700341615184542187218291 71550512422776813280827437)
              ·
                refine ⟨26831442158541304980310289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71550512422776813280827437 26831442158541304980310289)
                ·
                  refine ⟨20123581618905978735232717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26831442158541304980310289 20123581618905978735232717)
                  ·
                    refine ⟨7546343107089742025712269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20123581618905978735232717 7546343107089742025712269)
                    ·
                      refine ⟨2829878665158653259642101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546343107089742025712269 2829878665158653259642101)
                      ·
                        rfl

theorem cell23_5511169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_5511169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511169 prefixEnd_5511169 := by exact prefixLift 5511169
  have htrace : WordTrace (prefixWord ++ tailWord_5511169) baseStart_5511169 baseEnd_5511169 := by
    simpa [prefixWord, tailWord_5511169, baseEnd_5511169] using wordTrace_append hprefix tailTrace_5511169
  have hstable : (prefixWord ++ tailWord_5511169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511169).length < 2 ^ (prefixWord ++ tailWord_5511169).sum := by decide
  have hdescent : baseEnd_5511169 < baseStart_5511169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511212 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_5511212 : Nat := 118140960795 + 5511212 * 2 ^ 59
def prefixEnd_5511212 : Nat := 4983230072969 + 3 ^ 40 * 5511212 * 2
def baseEnd_5511212 : Nat := 2829900744826796591404403

theorem tailTrace_5511212 : CollatzResearch.WordTrace tailWord_5511212 prefixEnd_5511212 2829900744826796591404403 := by
  unfold tailWord_5511212
  simp only [CollatzResearch.WordTrace]
  refine ⟨100505207654913819459379945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134006943539885092612506593 100505207654913819459379945)
  ·
    refine ⟨75378905741185364594534959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100505207654913819459379945 75378905741185364594534959)
    ·
      refine ⟨113068358611778046891802439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75378905741185364594534959 113068358611778046891802439)
      ·
        refine ⟨169602537917667070337703659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113068358611778046891802439 169602537917667070337703659)
        ·
          refine ⟨254403806876500605506555489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169602537917667070337703659 254403806876500605506555489)
          ·
            refine ⟨190802855157375454129916617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254403806876500605506555489 190802855157375454129916617)
            ·
              refine ⟨143102141368031590597437463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190802855157375454129916617 143102141368031590597437463)
              ·
                refine ⟨214653212052047385896156195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143102141368031590597437463 214653212052047385896156195)
                ·
                  refine ⟨321979818078071078844234293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214653212052047385896156195 321979818078071078844234293)
                  ·
                    refine ⟨30185607944819163641646965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 321979818078071078844234293 30185607944819163641646965)
                    ·
                      refine ⟨2829900744826796591404403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30185607944819163641646965 2829900744826796591404403)
                      ·
                        rfl

theorem cell23_5511212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_5511212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511212 prefixEnd_5511212 := by exact prefixLift 5511212
  have htrace : WordTrace (prefixWord ++ tailWord_5511212) baseStart_5511212 baseEnd_5511212 := by
    simpa [prefixWord, tailWord_5511212, baseEnd_5511212] using wordTrace_append hprefix tailTrace_5511212
  have hstable : (prefixWord ++ tailWord_5511212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511212).length < 2 ^ (prefixWord ++ tailWord_5511212).sum := by decide
  have hdescent : baseEnd_5511212 < baseStart_5511212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511246 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_5511246 : Nat := 118140960795 + 5511246 * 2 ^ 59
def prefixEnd_5511246 : Nat := 4983230072969 + 3 ^ 40 * 5511246 * 2
def baseEnd_5511246 : Nat := 2829918203169049458379247

theorem tailTrace_5511246 : CollatzResearch.WordTrace tailWord_5511246 prefixEnd_5511246 2829918203169049458379247 := by
  unfold tailWord_5511246
  simp only [CollatzResearch.WordTrace]
  refine ⟨25126456923963057840687199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134007770261136308483665061 25126456923963057840687199)
  ·
    refine ⟨37689685385944586761030799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25126456923963057840687199 37689685385944586761030799)
    ·
      refine ⟨56534528078916880141546199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37689685385944586761030799 56534528078916880141546199)
      ·
        refine ⟨84801792118375320212319299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56534528078916880141546199 84801792118375320212319299)
        ·
          refine ⟨127202688177562980318478949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84801792118375320212319299 127202688177562980318478949)
          ·
            refine ⟨23850504033293058809714803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127202688177562980318478949 23850504033293058809714803)
            ·
              refine ⟨35775756049939588214572205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23850504033293058809714803 35775756049939588214572205)
              ·
                refine ⟨13415908518727345580464577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35775756049939588214572205 13415908518727345580464577)
                ·
                  refine ⟨10061931389045509185348433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13415908518727345580464577 10061931389045509185348433)
                  ·
                    refine ⟨7546448541784131889011325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10061931389045509185348433 7546448541784131889011325)
                    ·
                      refine ⟨2829918203169049458379247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546448541784131889011325 2829918203169049458379247)
                      ·
                        rfl

theorem cell23_5511246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_5511246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511246 prefixEnd_5511246 := by exact prefixLift 5511246
  have htrace : WordTrace (prefixWord ++ tailWord_5511246) baseStart_5511246 baseEnd_5511246 := by
    simpa [prefixWord, tailWord_5511246, baseEnd_5511246] using wordTrace_append hprefix tailTrace_5511246
  have hstable : (prefixWord ++ tailWord_5511246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511246).length < 2 ^ (prefixWord ++ tailWord_5511246).sum := by decide
  have hdescent : baseEnd_5511246 < baseStart_5511246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511279 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 3, 5]
def baseStart_5511279 : Nat := 118140960795 + 5511279 * 2 ^ 59
def prefixEnd_5511279 : Nat := 4983230072969 + 3 ^ 40 * 5511279 * 2
def baseEnd_5511279 : Nat := 943311716010215943088865

theorem tailTrace_5511279 : CollatzResearch.WordTrace tailWord_5511279 prefixEnd_5511279 943311716010215943088865 := by
  unfold tailWord_5511279
  simp only [CollatzResearch.WordTrace]
  refine ⟨201012859000584909361448891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134008572667056606240965927 201012859000584909361448891)
  ·
    refine ⟨301519288500877364042173337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201012859000584909361448891 301519288500877364042173337)
    ·
      refine ⟨226139466375658023031630003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301519288500877364042173337 226139466375658023031630003)
      ·
        refine ⟨339209199563487034547445005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226139466375658023031630003 339209199563487034547445005)
        ·
          refine ⟨127203449836307637955291877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339209199563487034547445005 127203449836307637955291877)
          ·
            refine ⟨23850646844307682116617227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127203449836307637955291877 23850646844307682116617227)
            ·
              refine ⟨35775970266461523174925841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23850646844307682116617227 35775970266461523174925841)
              ·
                refine ⟨26831977699846142381194381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35775970266461523174925841 26831977699846142381194381)
                ·
                  refine ⟨10061991637442303392947893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26831977699846142381194381 10061991637442303392947893)
                  ·
                    refine ⟨943311716010215943088865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10061991637442303392947893 943311716010215943088865)
                    ·
                      rfl

theorem cell23_5511279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_5511279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511279 prefixEnd_5511279 := by exact prefixLift 5511279
  have htrace : WordTrace (prefixWord ++ tailWord_5511279) baseStart_5511279 baseEnd_5511279 := by
    simpa [prefixWord, tailWord_5511279, baseEnd_5511279] using wordTrace_append hprefix tailTrace_5511279
  have hstable : (prefixWord ++ tailWord_5511279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511279).length < 2 ^ (prefixWord ++ tailWord_5511279).sum := by decide
  have hdescent : baseEnd_5511279 < baseStart_5511279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511293 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_5511293 : Nat := 118140960795 + 5511293 * 2 ^ 59
def prefixEnd_5511293 : Nat := 4983230072969 + 3 ^ 40 * 5511293 * 2
def baseEnd_5511293 : Nat := 2829942336759810774491531

theorem tailTrace_5511293 : CollatzResearch.WordTrace tailWord_5511293 prefixEnd_5511293 2829942336759810774491531 := by
  unfold tailWord_5511293
  simp only [CollatzResearch.WordTrace]
  refine ⟨201013369622534189752458533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134008913081689459834972355 201013369622534189752458533)
  ·
    refine ⟨37690006804225160578585975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201013369622534189752458533 37690006804225160578585975)
    ·
      refine ⟨56535010206337740867878963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37690006804225160578585975 56535010206337740867878963)
      ·
        refine ⟨84802515309506611301818445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56535010206337740867878963 84802515309506611301818445)
        ·
          refine ⟨31800943241064979238181917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84802515309506611301818445 31800943241064979238181917)
          ·
            refine ⟨11925353715399367214318219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31800943241064979238181917 11925353715399367214318219)
            ·
              refine ⟨17888030573099050821477329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925353715399367214318219 17888030573099050821477329)
              ·
                refine ⟨13416022929824288116107997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17888030573099050821477329 13416022929824288116107997)
                ·
                  refine ⟨5031008598684108043540499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13416022929824288116107997 5031008598684108043540499)
                  ·
                    refine ⟨7546512898026162065310749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031008598684108043540499 7546512898026162065310749)
                    ·
                      refine ⟨2829942336759810774491531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546512898026162065310749 2829942336759810774491531)
                      ·
                        rfl

theorem cell23_5511293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_5511293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511293 prefixEnd_5511293 := by exact prefixLift 5511293
  have htrace : WordTrace (prefixWord ++ tailWord_5511293) baseStart_5511293 baseEnd_5511293 := by
    simpa [prefixWord, tailWord_5511293, baseEnd_5511293] using wordTrace_append hprefix tailTrace_5511293
  have hstable : (prefixWord ++ tailWord_5511293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511293).length < 2 ^ (prefixWord ++ tailWord_5511293).sum := by decide
  have hdescent : baseEnd_5511293 < baseStart_5511293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511303 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_5511303 : Nat := 118140960795 + 5511303 * 2 ^ 59
def prefixEnd_5511303 : Nat := 4983230072969 + 3 ^ 40 * 5511303 * 2
def baseEnd_5511303 : Nat := 2829947471566355735366485

theorem tailTrace_5511303 : CollatzResearch.WordTrace tailWord_5511303 prefixEnd_5511303 2829947471566355735366485 := by
  unfold tailWord_5511303
  simp only [CollatzResearch.WordTrace]
  refine ⟨201013734352497961460322563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134009156234998640973548375 201013734352497961460322563)
  ·
    refine ⟨301520601528746942190483845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201013734352497961460322563 301520601528746942190483845)
    ·
      refine ⟨56535112786640051660715721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301520601528746942190483845 56535112786640051660715721)
      ·
        refine ⟨42401334589980038745536791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56535112786640051660715721 42401334589980038745536791)
        ·
          refine ⟨63602001884970058118305187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42401334589980038745536791 63602001884970058118305187)
          ·
            refine ⟨95403002827455087177457781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63602001884970058118305187 95403002827455087177457781)
            ·
              refine ⟨8944031515073914422886667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95403002827455087177457781 8944031515073914422886667)
              ·
                refine ⟨13416047272610871634330001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8944031515073914422886667 13416047272610871634330001)
                ·
                  refine ⟨10062035454458153725747501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13416047272610871634330001 10062035454458153725747501)
                  ·
                    refine ⟨3773263295421807647155313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10062035454458153725747501 3773263295421807647155313)
                    ·
                      refine ⟨2829947471566355735366485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773263295421807647155313 2829947471566355735366485)
                      ·
                        rfl

theorem cell23_5511303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_5511303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511303 prefixEnd_5511303 := by exact prefixLift 5511303
  have htrace : WordTrace (prefixWord ++ tailWord_5511303) baseStart_5511303 baseEnd_5511303 := by
    simpa [prefixWord, tailWord_5511303, baseEnd_5511303] using wordTrace_append hprefix tailTrace_5511303
  have hstable : (prefixWord ++ tailWord_5511303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511303).length < 2 ^ (prefixWord ++ tailWord_5511303).sum := by decide
  have hdescent : baseEnd_5511303 < baseStart_5511303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511353 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 3]
def baseStart_5511353 : Nat := 118140960795 + 5511353 * 2 ^ 59
def prefixEnd_5511353 : Nat := 4983230072969 + 3 ^ 40 * 5511353 * 2
def baseEnd_5511353 : Nat := 2829973145599080539741255

theorem tailTrace_5511353 : CollatzResearch.WordTrace tailWord_5511353 prefixEnd_5511353 2829973145599080539741255 := by
  unfold tailWord_5511353
  simp only [CollatzResearch.WordTrace]
  refine ⟨201015558002316819999642713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134010372001544546666428475 201015558002316819999642713)
  ·
    refine ⟨150761668501737614999732035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201015558002316819999642713 150761668501737614999732035)
    ·
      refine ⟨226142502752606422499598053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150761668501737614999732035 226142502752606422499598053)
      ·
        refine ⟨42401719266113704218674635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226142502752606422499598053 42401719266113704218674635)
        ·
          refine ⟨63602578899170556328011953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42401719266113704218674635 63602578899170556328011953)
          ·
            refine ⟨47701934174377917246008965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63602578899170556328011953 47701934174377917246008965)
            ·
              refine ⟨8944112657695859483626681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47701934174377917246008965 8944112657695859483626681)
              ·
                refine ⟨6708084493271894612720011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8944112657695859483626681 6708084493271894612720011)
                ·
                  refine ⟨10062126739907841919080017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6708084493271894612720011 10062126739907841919080017)
                  ·
                    refine ⟨7546595054930881439310013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10062126739907841919080017 7546595054930881439310013)
                    ·
                      refine ⟨2829973145599080539741255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546595054930881439310013 2829973145599080539741255)
                      ·
                        rfl

theorem cell23_5511353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_5511353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511353 prefixEnd_5511353 := by exact prefixLift 5511353
  have htrace : WordTrace (prefixWord ++ tailWord_5511353) baseStart_5511353 baseEnd_5511353 := by
    simpa [prefixWord, tailWord_5511353, baseEnd_5511353] using wordTrace_append hprefix tailTrace_5511353
  have hstable : (prefixWord ++ tailWord_5511353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511353).length < 2 ^ (prefixWord ++ tailWord_5511353).sum := by decide
  have hdescent : baseEnd_5511353 < baseStart_5511353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511356 : List Nat := [2, 2, 2, 3, 3, 1, 1, 9]
def baseStart_5511356 : Nat := 118140960795 + 5511356 * 2 ^ 59
def prefixEnd_5511356 : Nat := 4983230072969 + 3 ^ 40 * 5511356 * 2
def baseEnd_5511356 : Nat := 104813877260779408444583

theorem tailTrace_5511356 : CollatzResearch.WordTrace tailWord_5511356 prefixEnd_5511356 104813877260779408444583 := by
  unfold tailWord_5511356
  simp only [CollatzResearch.WordTrace]
  refine ⟨100507833710652975756000961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134010444947537301008001281 100507833710652975756000961)
  ·
    refine ⟨75380875282989731817000721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100507833710652975756000961 75380875282989731817000721)
    ·
      refine ⟨56535656462242298862750541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75380875282989731817000721 56535656462242298862750541)
      ·
        refine ⟨21200871173340862073531453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56535656462242298862750541 21200871173340862073531453)
        ·
          refine ⟨7950326690002823277574295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21200871173340862073531453 7950326690002823277574295)
          ·
            refine ⟨11925490035004234916361443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950326690002823277574295 11925490035004234916361443)
            ·
              refine ⟨17888235052506352374542165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925490035004234916361443 17888235052506352374542165)
              ·
                refine ⟨104813877260779408444583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17888235052506352374542165 104813877260779408444583)
                ·
                  rfl

theorem cell23_5511356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 9].length) (baseStart_5511356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511356 prefixEnd_5511356 := by exact prefixLift 5511356
  have htrace : WordTrace (prefixWord ++ tailWord_5511356) baseStart_5511356 baseEnd_5511356 := by
    simpa [prefixWord, tailWord_5511356, baseEnd_5511356] using wordTrace_append hprefix tailTrace_5511356
  have hstable : (prefixWord ++ tailWord_5511356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511356).length < 2 ^ (prefixWord ++ tailWord_5511356).sum := by decide
  have hdescent : baseEnd_5511356 < baseStart_5511356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511361 : List Nat := [1, 2, 6, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5511361 : Nat := 118140960795 + 5511361 * 2 ^ 59
def prefixEnd_5511361 : Nat := 4983230072969 + 3 ^ 40 * 5511361 * 2
def baseEnd_5511361 : Nat := 2829977253444316508441219

theorem tailTrace_5511361 : CollatzResearch.WordTrace tailWord_5511361 prefixEnd_5511361 2829977253444316508441219 := by
  unfold tailWord_5511361
  simp only [CollatzResearch.WordTrace]
  refine ⟨201015849786287837365933937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134010566524191891577289291 201015849786287837365933937)
  ·
    refine ⟨150761887339715878024450453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201015849786287837365933937 150761887339715878024450453)
    ·
      refine ⟨7066963469049181782396115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150761887339715878024450453 7066963469049181782396115)
      ·
        refine ⟨10600445203573772673594173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7066963469049181782396115 10600445203573772673594173)
        ·
          refine ⟨3975166951340164752597815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10600445203573772673594173 3975166951340164752597815)
          ·
            refine ⟨5962750427010247128896723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975166951340164752597815 5962750427010247128896723)
            ·
              refine ⟨8944125640515370693345085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5962750427010247128896723 8944125640515370693345085)
              ·
                refine ⟨3354047115193264010004407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8944125640515370693345085 3354047115193264010004407)
                ·
                  refine ⟨5031070672789896015006611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354047115193264010004407 5031070672789896015006611)
                  ·
                    refine ⟨7546606009184844022509917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031070672789896015006611 7546606009184844022509917)
                    ·
                      refine ⟨2829977253444316508441219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546606009184844022509917 2829977253444316508441219)
                      ·
                        rfl

theorem cell23_5511361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5511361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511361 prefixEnd_5511361 := by exact prefixLift 5511361
  have htrace : WordTrace (prefixWord ++ tailWord_5511361) baseStart_5511361 baseEnd_5511361 := by
    simpa [prefixWord, tailWord_5511361, baseEnd_5511361] using wordTrace_append hprefix tailTrace_5511361
  have hstable : (prefixWord ++ tailWord_5511361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511361).length < 2 ^ (prefixWord ++ tailWord_5511361).sum := by decide
  have hdescent : baseEnd_5511361 < baseStart_5511361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511383 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_5511383 : Nat := 118140960795 + 5511383 * 2 ^ 59
def prefixEnd_5511383 : Nat := 4983230072969 + 3 ^ 40 * 5511383 * 2
def baseEnd_5511383 : Nat := 2829988550018715422366117

theorem tailTrace_5511383 : CollatzResearch.WordTrace tailWord_5511383 prefixEnd_5511383 2829988550018715422366117 := by
  unfold tailWord_5511383
  simp only [CollatzResearch.WordTrace]
  refine ⟨201016652192208135123234803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134011101461472090082156535 201016652192208135123234803)
  ·
    refine ⟨301524978288312202684852205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201016652192208135123234803 301524978288312202684852205)
    ·
      refine ⟨113071866858117076006819577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301524978288312202684852205 113071866858117076006819577)
      ·
        refine ⟨84803900143587807005114683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113071866858117076006819577 84803900143587807005114683)
        ·
          refine ⟨127205850215381710507672025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84803900143587807005114683 127205850215381710507672025)
          ·
            refine ⟨95404387661536282880754019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127205850215381710507672025 95404387661536282880754019)
            ·
              refine ⟨143106581492304424321131029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95404387661536282880754019 143106581492304424321131029)
              ·
                refine ⟨6708121007451769890053017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143106581492304424321131029 6708121007451769890053017)
                ·
                  refine ⟨5031090755588827417539763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6708121007451769890053017 5031090755588827417539763)
                  ·
                    refine ⟨7546636133383241126309645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031090755588827417539763 7546636133383241126309645)
                    ·
                      refine ⟨2829988550018715422366117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546636133383241126309645 2829988550018715422366117)
                      ·
                        rfl

theorem cell23_5511383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_5511383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511383 prefixEnd_5511383 := by exact prefixLift 5511383
  have htrace : WordTrace (prefixWord ++ tailWord_5511383) baseStart_5511383 baseEnd_5511383 := by
    simpa [prefixWord, tailWord_5511383, baseEnd_5511383] using wordTrace_append hprefix tailTrace_5511383
  have hstable : (prefixWord ++ tailWord_5511383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511383).length < 2 ^ (prefixWord ++ tailWord_5511383).sum := by decide
  have hdescent : baseEnd_5511383 < baseStart_5511383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511384 : List Nat := [2, 1, 2, 2, 4, 2, 3, 2, 1, 2, 2]
def baseStart_5511384 : Nat := 118140960795 + 5511384 * 2 ^ 59
def prefixEnd_5511384 : Nat := 4983230072969 + 3 ^ 40 * 5511384 * 2
def baseEnd_5511384 : Nat := 2829989063499369918453613

theorem tailTrace_5511384 : CollatzResearch.WordTrace tailWord_5511384 prefixEnd_5511384 2829989063499369918453613 := by
  unfold tailWord_5511384
  simp only [CollatzResearch.WordTrace]
  refine ⟨100508344332602256147010603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134011125776803008196014137 100508344332602256147010603)
  ·
    refine ⟨150762516498903384220515905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100508344332602256147010603 150762516498903384220515905)
    ·
      refine ⟨113071887374177538165386929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150762516498903384220515905 113071887374177538165386929)
      ·
        refine ⟨84803915530633153624040197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113071887374177538165386929 84803915530633153624040197)
        ·
          refine ⟨15900734161993716304507537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84803915530633153624040197 15900734161993716304507537)
          ·
            refine ⟨11925550621495287228380653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15900734161993716304507537 11925550621495287228380653)
            ·
              refine ⟨4472081483060732710642745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11925550621495287228380653 4472081483060732710642745)
              ·
                refine ⟨3354061112295549532982059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4472081483060732710642745 3354061112295549532982059)
                ·
                  refine ⟨5031091668443324299473089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354061112295549532982059 5031091668443324299473089)
                  ·
                    refine ⟨3773318751332493224604817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5031091668443324299473089 3773318751332493224604817)
                    ·
                      refine ⟨2829989063499369918453613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773318751332493224604817 2829989063499369918453613)
                      ·
                        rfl

theorem cell23_5511384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_5511384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511384 prefixEnd_5511384 := by exact prefixLift 5511384
  have htrace : WordTrace (prefixWord ++ tailWord_5511384) baseStart_5511384 baseEnd_5511384 := by
    simpa [prefixWord, tailWord_5511384, baseEnd_5511384] using wordTrace_append hprefix tailTrace_5511384
  have hstable : (prefixWord ++ tailWord_5511384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511384).length < 2 ^ (prefixWord ++ tailWord_5511384).sum := by decide
  have hdescent : baseEnd_5511384 < baseStart_5511384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511393 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_5511393 : Nat := 118140960795 + 5511393 * 2 ^ 59
def prefixEnd_5511393 : Nat := 4983230072969 + 3 ^ 40 * 5511393 * 2
def baseEnd_5511393 : Nat := 2829993684825260383241071

theorem tailTrace_5511393 : CollatzResearch.WordTrace tailWord_5511393 prefixEnd_5511393 2829993684825260383241071 := by
  unfold tailWord_5511393
  simp only [CollatzResearch.WordTrace]
  refine ⟨201017016922171906831098833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134011344614781271220732555 201017016922171906831098833)
  ·
    refine ⟨150762762691628930123324125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201017016922171906831098833 150762762691628930123324125)
    ·
      refine ⟨56536036009360848796246547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150762762691628930123324125 56536036009360848796246547)
      ·
        refine ⟨84804054014041273194369821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56536036009360848796246547 84804054014041273194369821)
        ·
          refine ⟨31801520255265477447888683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84804054014041273194369821 31801520255265477447888683)
          ·
            refine ⟨47702280382898216171833025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31801520255265477447888683 47702280382898216171833025)
            ·
              refine ⟨35776710287173662128874769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47702280382898216171833025 35776710287173662128874769)
              ·
                refine ⟨26832532715380246596656077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35776710287173662128874769 26832532715380246596656077)
                ·
                  refine ⟨10062199768267592473746029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26832532715380246596656077 10062199768267592473746029)
                  ·
                    refine ⟨3773324913100347177654761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10062199768267592473746029 3773324913100347177654761)
                    ·
                      refine ⟨2829993684825260383241071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773324913100347177654761 2829993684825260383241071)
                      ·
                        rfl

theorem cell23_5511393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_5511393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511393 prefixEnd_5511393 := by exact prefixLift 5511393
  have htrace : WordTrace (prefixWord ++ tailWord_5511393) baseStart_5511393 baseEnd_5511393 := by
    simpa [prefixWord, tailWord_5511393, baseEnd_5511393] using wordTrace_append hprefix tailTrace_5511393
  have hstable : (prefixWord ++ tailWord_5511393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511393).length < 2 ^ (prefixWord ++ tailWord_5511393).sum := by decide
  have hdescent : baseEnd_5511393 < baseStart_5511393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511394 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5511394 : Nat := 118140960795 + 5511394 * 2 ^ 59
def prefixEnd_5511394 : Nat := 4983230072969 + 3 ^ 40 * 5511394 * 2
def baseEnd_5511394 : Nat := 943331399435304959776189

theorem tailTrace_5511394 : CollatzResearch.WordTrace tailWord_5511394 prefixEnd_5511394 943331399435304959776189 := by
  unfold tailWord_5511394
  simp only [CollatzResearch.WordTrace]
  refine ⟨50254263348792071000471309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134011368930112189334590157 50254263348792071000471309)
  ·
    refine ⟨18845348755797026625176741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50254263348792071000471309 18845348755797026625176741)
    ·
      refine ⟨3533502891711942492220639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18845348755797026625176741 3533502891711942492220639)
      ·
        refine ⟨5300254337567913738330959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533502891711942492220639 5300254337567913738330959)
        ·
          refine ⟨7950381506351870607496439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300254337567913738330959 7950381506351870607496439)
          ·
            refine ⟨11925572259527805911244659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950381506351870607496439 11925572259527805911244659)
            ·
              refine ⟨17888358389291708866866989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925572259527805911244659 17888358389291708866866989)
              ·
                refine ⟨6708134395984390825075121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17888358389291708866866989 6708134395984390825075121)
                ·
                  refine ⟨5031100796988293118806341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6708134395984390825075121 5031100796988293118806341)
                  ·
                    refine ⟨943331399435304959776189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5031100796988293118806341 943331399435304959776189)
                    ·
                      rfl

theorem cell23_5511394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5511394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511394 prefixEnd_5511394 := by exact prefixLift 5511394
  have htrace : WordTrace (prefixWord ++ tailWord_5511394) baseStart_5511394 baseEnd_5511394 := by
    simpa [prefixWord, tailWord_5511394, baseEnd_5511394] using wordTrace_append hprefix tailTrace_5511394
  have hstable : (prefixWord ++ tailWord_5511394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511394).length < 2 ^ (prefixWord ++ tailWord_5511394).sum := by decide
  have hdescent : baseEnd_5511394 < baseStart_5511394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511400 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_5511400 : Nat := 118140960795 + 5511400 * 2 ^ 59
def prefixEnd_5511400 : Nat := 4983230072969 + 3 ^ 40 * 5511400 * 2
def baseEnd_5511400 : Nat := 2829997279189841855853539

theorem tailTrace_5511400 : CollatzResearch.WordTrace tailWord_5511400 prefixEnd_5511400 2829997279189841855853539 := by
  unfold tailWord_5511400
  simp only [CollatzResearch.WordTrace]
  refine ⟨100508636116573273513301827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134011514822097698017735769 100508636116573273513301827)
  ·
    refine ⟨150762954174859910269952741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100508636116573273513301827 150762954174859910269952741)
    ·
      refine ⟨28268053907786233175616139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150762954174859910269952741 28268053907786233175616139)
      ·
        refine ⟨42402080861679349763424209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28268053907786233175616139 42402080861679349763424209)
        ·
          refine ⟨31801560646259512322568157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42402080861679349763424209 31801560646259512322568157)
          ·
            refine ⟨11925585242347317120963059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31801560646259512322568157 11925585242347317120963059)
            ·
              refine ⟨17888377863520975681444589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925585242347317120963059 17888377863520975681444589)
              ·
                refine ⟨6708141698820365880541721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17888377863520975681444589 6708141698820365880541721)
                ·
                  refine ⟨5031106274115274410406291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6708141698820365880541721 5031106274115274410406291)
                  ·
                    refine ⟨7546659411172911615609437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031106274115274410406291 7546659411172911615609437)
                    ·
                      refine ⟨2829997279189841855853539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546659411172911615609437 2829997279189841855853539)
                      ·
                        rfl

theorem cell23_5511400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_5511400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511400 prefixEnd_5511400 := by exact prefixLift 5511400
  have htrace : WordTrace (prefixWord ++ tailWord_5511400) baseStart_5511400 baseEnd_5511400 := by
    simpa [prefixWord, tailWord_5511400, baseEnd_5511400] using wordTrace_append hprefix tailTrace_5511400
  have hstable : (prefixWord ++ tailWord_5511400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511400).length < 2 ^ (prefixWord ++ tailWord_5511400).sum := by decide
  have hdescent : baseEnd_5511400 < baseStart_5511400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511410 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_5511410 : Nat := 118140960795 + 5511410 * 2 ^ 59
def prefixEnd_5511410 : Nat := 4983230072969 + 3 ^ 40 * 5511410 * 2
def baseEnd_5511410 : Nat := 2830002413996386816728493

theorem tailTrace_5511410 : CollatzResearch.WordTrace tailWord_5511410 prefixEnd_5511410 2830002413996386816728493 := by
  unfold tailWord_5511410
  simp only [CollatzResearch.WordTrace]
  refine ⟨50254409240777579683616921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134011757975406879156311789 50254409240777579683616921)
  ·
    refine ⟨37690806930583184762712691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50254409240777579683616921 37690806930583184762712691)
    ·
      refine ⟨56536210395874777144069037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37690806930583184762712691 56536210395874777144069037)
      ·
        refine ⟨21201078898453041429025889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56536210395874777144069037 21201078898453041429025889)
        ·
          refine ⟨15900809173839781071769417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21201078898453041429025889 15900809173839781071769417)
          ·
            refine ⟨11925606880379835803827063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15900809173839781071769417 11925606880379835803827063)
            ·
              refine ⟨17888410320569753705740595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925606880379835803827063 17888410320569753705740595)
              ·
                refine ⟨26832615480854630558610893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17888410320569753705740595 26832615480854630558610893)
                ·
                  refine ⟨10062230805320486459479085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26832615480854630558610893 10062230805320486459479085)
                  ·
                    refine ⟨3773336551995182422304657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10062230805320486459479085 3773336551995182422304657)
                    ·
                      refine ⟨2830002413996386816728493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773336551995182422304657 2830002413996386816728493)
                      ·
                        rfl

theorem cell23_5511410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_5511410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511410 prefixEnd_5511410 := by exact prefixLift 5511410
  have htrace : WordTrace (prefixWord ++ tailWord_5511410) baseStart_5511410 baseEnd_5511410 := by
    simpa [prefixWord, tailWord_5511410, baseEnd_5511410] using wordTrace_append hprefix tailTrace_5511410
  have hstable : (prefixWord ++ tailWord_5511410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511410).length < 2 ^ (prefixWord ++ tailWord_5511410).sum := by decide
  have hdescent : baseEnd_5511410 < baseStart_5511410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511423 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 1, 4, 2]
def baseStart_5511423 : Nat := 118140960795 + 5511423 * 2 ^ 59
def prefixEnd_5511423 : Nat := 4983230072969 + 3 ^ 40 * 5511423 * 2
def baseEnd_5511423 : Nat := 2830009089244895265865933

theorem tailTrace_5511423 : CollatzResearch.WordTrace tailWord_5511423 prefixEnd_5511423 2830009089244895265865933 := by
  unfold tailWord_5511423
  simp only [CollatzResearch.WordTrace]
  refine ⟨201018111112063221954690923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134012074074708814636460615 201018111112063221954690923)
  ·
    refine ⟨301527166668094832932036385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201018111112063221954690923 301527166668094832932036385)
    ·
      refine ⟨226145375001071124699027289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301527166668094832932036385 226145375001071124699027289)
      ·
        refine ⟨169609031250803343524270467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226145375001071124699027289 169609031250803343524270467)
        ·
          refine ⟨254413546876205015286405701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169609031250803343524270467 254413546876205015286405701)
          ·
            refine ⟨47702540039288440366201069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254413546876205015286405701 47702540039288440366201069)
            ·
              refine ⟨17888452514733165137325401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47702540039288440366201069 17888452514733165137325401)
              ·
                refine ⟨13416339386049873852994051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17888452514733165137325401 13416339386049873852994051)
                ·
                  refine ⟨20124509079074810779491077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13416339386049873852994051 20124509079074810779491077)
                  ·
                    refine ⟨3773345452326527021154577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20124509079074810779491077 3773345452326527021154577)
                    ·
                      refine ⟨2830009089244895265865933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773345452326527021154577 2830009089244895265865933)
                      ·
                        rfl

theorem cell23_5511423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_5511423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511423 prefixEnd_5511423 := by exact prefixLift 5511423
  have htrace : WordTrace (prefixWord ++ tailWord_5511423) baseStart_5511423 baseEnd_5511423 := by
    simpa [prefixWord, tailWord_5511423, baseEnd_5511423] using wordTrace_append hprefix tailTrace_5511423
  have hstable : (prefixWord ++ tailWord_5511423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511423).length < 2 ^ (prefixWord ++ tailWord_5511423).sum := by decide
  have hdescent : baseEnd_5511423 < baseStart_5511423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511429 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 11]
def baseStart_5511429 : Nat := 118140960795 + 5511429 * 2 ^ 59
def prefixEnd_5511429 : Nat := 4983230072969 + 3 ^ 40 * 5511429 * 2
def baseEnd_5511429 : Nat := 314445796680980249154545

theorem tailTrace_5511429 : CollatzResearch.WordTrace tailWord_5511429 prefixEnd_5511429 314445796680980249154545 := by
  unfold tailWord_5511429
  simp only [CollatzResearch.WordTrace]
  refine ⟨201018329950041484979409341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134012219966694323319606227 201018329950041484979409341)
  ·
    refine ⟨75381873731265556867278503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201018329950041484979409341 75381873731265556867278503)
    ·
      refine ⟨113072810596898335300917755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75381873731265556867278503 113072810596898335300917755)
      ·
        refine ⟨169609215895347502951376633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113072810596898335300917755 169609215895347502951376633)
        ·
          refine ⟨127206911921510627213532475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169609215895347502951376633 127206911921510627213532475)
          ·
            refine ⟨190810367882265940820298713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127206911921510627213532475 190810367882265940820298713)
            ·
              refine ⟨143107775911699455615224035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190810367882265940820298713 143107775911699455615224035)
              ·
                refine ⟨214661663867549183422836053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143107775911699455615224035 214661663867549183422836053)
                ·
                  refine ⟨314445796680980249154545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 214661663867549183422836053 314445796680980249154545)
                  ·
                    rfl

theorem cell23_5511429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_5511429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511429 prefixEnd_5511429 := by exact prefixLift 5511429
  have htrace : WordTrace (prefixWord ++ tailWord_5511429) baseStart_5511429 baseEnd_5511429 := by
    simpa [prefixWord, tailWord_5511429, baseEnd_5511429] using wordTrace_append hprefix tailTrace_5511429
  have hstable : (prefixWord ++ tailWord_5511429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511429).length < 2 ^ (prefixWord ++ tailWord_5511429).sum := by decide
  have hdescent : baseEnd_5511429 < baseStart_5511429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511436 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_5511436 : Nat := 118140960795 + 5511436 * 2 ^ 59
def prefixEnd_5511436 : Nat := 4983230072969 + 3 ^ 40 * 5511436 * 2
def baseEnd_5511436 : Nat := 2830015764493403715003373

theorem tailTrace_5511436 : CollatzResearch.WordTrace tailWord_5511436 prefixEnd_5511436 2830015764493403715003373 := by
  unfold tailWord_5511436
  simp only [CollatzResearch.WordTrace]
  refine ⟨100509292630508062587457081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134012390174010750116609441 100509292630508062587457081)
  ·
    refine ⟨75381969472881046940592811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100509292630508062587457081 75381969472881046940592811)
    ·
      refine ⟨113072954209321570410889217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75381969472881046940592811 113072954209321570410889217)
      ·
        refine ⟨84804715656991177808166913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113072954209321570410889217 84804715656991177808166913)
        ·
          refine ⟨63603536742743383356125185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84804715656991177808166913 63603536742743383356125185)
          ·
            refine ⟨47702652557057537517093889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63603536742743383356125185 47702652557057537517093889)
            ·
              refine ⟨35776989417793153137820417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47702652557057537517093889 35776989417793153137820417)
              ·
                refine ⟨26832742063344864853365313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35776989417793153137820417 26832742063344864853365313)
                ·
                  refine ⟨20124556547508648640023985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26832742063344864853365313 20124556547508648640023985)
                  ·
                    refine ⟨15093417410631486480017989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20124556547508648640023985 15093417410631486480017989)
                    ·
                      refine ⟨2830015764493403715003373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15093417410631486480017989 2830015764493403715003373)
                      ·
                        rfl

theorem cell23_5511436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_5511436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511436 prefixEnd_5511436 := by exact prefixLift 5511436
  have htrace : WordTrace (prefixWord ++ tailWord_5511436) baseStart_5511436 baseEnd_5511436 := by
    simpa [prefixWord, tailWord_5511436, baseEnd_5511436] using wordTrace_append hprefix tailTrace_5511436
  have hstable : (prefixWord ++ tailWord_5511436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511436).length < 2 ^ (prefixWord ++ tailWord_5511436).sum := by decide
  have hdescent : baseEnd_5511436 < baseStart_5511436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511439 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_5511439 : Nat := 118140960795 + 5511439 * 2 ^ 59
def prefixEnd_5511439 : Nat := 4983230072969 + 3 ^ 40 * 5511439 * 2
def baseEnd_5511439 : Nat := 2830017304935367203265859

theorem tailTrace_5511439 : CollatzResearch.WordTrace tailWord_5511439 prefixEnd_5511439 2830017304935367203265859 := by
  unfold tailWord_5511439
  simp only [CollatzResearch.WordTrace]
  refine ⟨201018694680005256687273371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134012463120003504458182247 201018694680005256687273371)
  ·
    refine ⟨301528042020007885030910057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201018694680005256687273371 301528042020007885030910057)
    ·
      refine ⟨226146031515005913773182543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301528042020007885030910057 226146031515005913773182543)
      ·
        refine ⟨339219047272508870659773815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226146031515005913773182543 339219047272508870659773815)
        ·
          refine ⟨508828570908763305989660723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339219047272508870659773815 508828570908763305989660723)
          ·
            refine ⟨763242856363144958984491085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508828570908763305989660723 763242856363144958984491085)
            ·
              refine ⟨286216071136179359619184157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 763242856363144958984491085 286216071136179359619184157)
              ·
                refine ⟨107331026676067259857194059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286216071136179359619184157 107331026676067259857194059)
                ·
                  refine ⟨160996540014100889785791089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107331026676067259857194059 160996540014100889785791089)
                  ·
                    refine ⟨120747405010575667339343317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160996540014100889785791089 120747405010575667339343317)
                    ·
                      refine ⟨2830017304935367203265859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120747405010575667339343317 2830017304935367203265859)
                      ·
                        rfl

theorem cell23_5511439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_5511439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511439 prefixEnd_5511439 := by exact prefixLift 5511439
  have htrace : WordTrace (prefixWord ++ tailWord_5511439) baseStart_5511439 baseEnd_5511439 := by
    simpa [prefixWord, tailWord_5511439, baseEnd_5511439] using wordTrace_append hprefix tailTrace_5511439
  have hstable : (prefixWord ++ tailWord_5511439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511439).length < 2 ^ (prefixWord ++ tailWord_5511439).sum := by decide
  have hdescent : baseEnd_5511439 < baseStart_5511439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511523 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 3, 4]
def baseStart_5511523 : Nat := 118140960795 + 5511523 * 2 ^ 59
def prefixEnd_5511523 : Nat := 4983230072969 + 3 ^ 40 * 5511523 * 2
def baseEnd_5511523 : Nat := 943353479103448291538491

theorem tailTrace_5511523 : CollatzResearch.WordTrace tailWord_5511523 prefixEnd_5511523 943353479103448291538491 := by
  unfold tailWord_5511523
  simp only [CollatzResearch.WordTrace]
  refine ⟨201021758411700939033331223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134014505607800626022220815 201021758411700939033331223)
  ·
    refine ⟨301532637617551408549996835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201021758411700939033331223 301532637617551408549996835)
    ·
      refine ⟨452298956426327112824995253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301532637617551408549996835 452298956426327112824995253)
      ·
        refine ⟨42403027164968166827343305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 452298956426327112824995253 42403027164968166827343305)
        ·
          refine ⟨31802270373726125120507479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42403027164968166827343305 31802270373726125120507479)
          ·
            refine ⟨47703405560589187680761219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31802270373726125120507479 47703405560589187680761219)
            ·
              refine ⟨71555108340883781521141829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47703405560589187680761219 71555108340883781521141829)
              ·
                refine ⟨13416582813915709035214093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71555108340883781521141829 13416582813915709035214093)
                ·
                  refine ⟨5031218555218390888205285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13416582813915709035214093 5031218555218390888205285)
                  ·
                    refine ⟨943353479103448291538491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5031218555218390888205285 943353479103448291538491)
                    ·
                      rfl

theorem cell23_5511523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 4].length) (baseStart_5511523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511523 prefixEnd_5511523 := by exact prefixLift 5511523
  have htrace : WordTrace (prefixWord ++ tailWord_5511523) baseStart_5511523 baseEnd_5511523 := by
    simpa [prefixWord, tailWord_5511523, baseEnd_5511523] using wordTrace_append hprefix tailTrace_5511523
  have hstable : (prefixWord ++ tailWord_5511523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511523).length < 2 ^ (prefixWord ++ tailWord_5511523).sum := by decide
  have hdescent : baseEnd_5511523 < baseStart_5511523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511533 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_5511533 : Nat := 118140960795 + 5511533 * 2 ^ 59
def prefixEnd_5511533 : Nat := 4983230072969 + 3 ^ 40 * 5511533 * 2
def baseEnd_5511533 : Nat := 2830065572116889835490427

theorem tailTrace_5511533 : CollatzResearch.WordTrace tailWord_5511533 prefixEnd_5511533 2830065572116889835490427 := by
  unfold tailWord_5511533
  simp only [CollatzResearch.WordTrace]
  refine ⟨201022123141664710741195253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134014748761109807160796835 201022123141664710741195253)
  ·
    refine ⟨18845824044531066631987055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201022123141664710741195253 18845824044531066631987055)
    ·
      refine ⟨28268736066796599947980583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18845824044531066631987055 28268736066796599947980583)
      ·
        refine ⟨42403104100194899921970875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28268736066796599947980583 42403104100194899921970875)
        ·
          refine ⟨63604656150292349882956313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42403104100194899921970875 63604656150292349882956313)
          ·
            refine ⟨47703492112719262412217235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63604656150292349882956313 47703492112719262412217235)
            ·
              refine ⟨71555238169078893618325853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47703492112719262412217235 71555238169078893618325853)
              ·
                refine ⟨26833214313404585106872195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71555238169078893618325853 26833214313404585106872195)
                ·
                  refine ⟨40249821470106877660308293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26833214313404585106872195 40249821470106877660308293)
                  ·
                    refine ⟨7546841525645039561307805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40249821470106877660308293 7546841525645039561307805)
                    ·
                      refine ⟨2830065572116889835490427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546841525645039561307805 2830065572116889835490427)
                      ·
                        rfl

theorem cell23_5511533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_5511533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511533 prefixEnd_5511533 := by exact prefixLift 5511533
  have htrace : WordTrace (prefixWord ++ tailWord_5511533) baseStart_5511533 baseEnd_5511533 := by
    simpa [prefixWord, tailWord_5511533, baseEnd_5511533] using wordTrace_append hprefix tailTrace_5511533
  have hstable : (prefixWord ++ tailWord_5511533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511533).length < 2 ^ (prefixWord ++ tailWord_5511533).sum := by decide
  have hdescent : baseEnd_5511533 < baseStart_5511533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511536 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 8]
def baseStart_5511536 : Nat := 118140960795 + 5511536 * 2 ^ 59
def prefixEnd_5511536 : Nat := 4983230072969 + 3 ^ 40 * 5511536 * 2
def baseEnd_5511536 : Nat := 314451901395428147083657

theorem tailTrace_5511536 : CollatzResearch.WordTrace tailWord_5511536 prefixEnd_5511536 314451901395428147083657 := by
  unfold tailWord_5511536
  simp only [CollatzResearch.WordTrace]
  refine ⟨100511116280326921126777231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134014821707102561502369641 100511116280326921126777231)
  ·
    refine ⟨150766674420490381690165847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100511116280326921126777231 150766674420490381690165847)
    ·
      refine ⟨226150011630735572535248771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150766674420490381690165847 226150011630735572535248771)
      ·
        refine ⟨339225017446103358802873157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226150011630735572535248771 339225017446103358802873157)
        ·
          refine ⟨63604690771144379775538717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339225017446103358802873157 63604690771144379775538717)
          ·
            refine ⟨23851759039179142415827019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63604690771144379775538717 23851759039179142415827019)
            ·
              refine ⟨35777638558768713623740529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23851759039179142415827019 35777638558768713623740529)
              ·
                refine ⟨26833228919076535217805397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35777638558768713623740529 26833228919076535217805397)
                ·
                  refine ⟨314451901395428147083657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26833228919076535217805397 314451901395428147083657)
                  ·
                    rfl

theorem cell23_5511536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 8].length) (baseStart_5511536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511536 prefixEnd_5511536 := by exact prefixLift 5511536
  have htrace : WordTrace (prefixWord ++ tailWord_5511536) baseStart_5511536 baseEnd_5511536 := by
    simpa [prefixWord, tailWord_5511536, baseEnd_5511536] using wordTrace_append hprefix tailTrace_5511536
  have hstable : (prefixWord ++ tailWord_5511536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511536).length < 2 ^ (prefixWord ++ tailWord_5511536).sum := by decide
  have hdescent : baseEnd_5511536 < baseStart_5511536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511553 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 8]
def baseStart_5511553 : Nat := 118140960795 + 5511553 * 2 ^ 59
def prefixEnd_5511553 : Nat := 4983230072969 + 3 ^ 40 * 5511553 * 2
def baseEnd_5511553 : Nat := 314452871303331084137815

theorem tailTrace_5511553 : CollatzResearch.WordTrace tailWord_5511553 prefixEnd_5511553 314452871303331084137815 := by
  unfold tailWord_5511553
  simp only [CollatzResearch.WordTrace]
  refine ⟨201022852601592254156923313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134015235067728169437948875 201022852601592254156923313)
  ·
    refine ⟨150767139451194190617692485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201022852601592254156923313 150767139451194190617692485)
    ·
      refine ⟨28268838647098910740817341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150767139451194190617692485 28268838647098910740817341)
      ·
        refine ⟨10600814492662091527806503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28268838647098910740817341 10600814492662091527806503)
        ·
          refine ⟨15901221738993137291709755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10600814492662091527806503 15901221738993137291709755)
          ·
            refine ⟨23851832608489705937564633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15901221738993137291709755 23851832608489705937564633)
            ·
              refine ⟨17888874456367279453173475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23851832608489705937564633 17888874456367279453173475)
              ·
                refine ⟨26833311684550919179760213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17888874456367279453173475 26833311684550919179760213)
                ·
                  refine ⟨314452871303331084137815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26833311684550919179760213 314452871303331084137815)
                  ·
                    rfl

theorem cell23_5511553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 8].length) (baseStart_5511553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511553 prefixEnd_5511553 := by exact prefixLift 5511553
  have htrace : WordTrace (prefixWord ++ tailWord_5511553) baseStart_5511553 baseEnd_5511553 := by
    simpa [prefixWord, tailWord_5511553, baseEnd_5511553] using wordTrace_append hprefix tailTrace_5511553
  have hstable : (prefixWord ++ tailWord_5511553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511553).length < 2 ^ (prefixWord ++ tailWord_5511553).sum := by decide
  have hdescent : baseEnd_5511553 < baseStart_5511553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511583 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 3, 5]
def baseStart_5511583 : Nat := 118140960795 + 5511583 * 2 ^ 59
def prefixEnd_5511583 : Nat := 4983230072969 + 3 ^ 40 * 5511583 * 2
def baseEnd_5511583 : Nat := 943363748716538213288399

theorem tailTrace_5511583 : CollatzResearch.WordTrace tailWord_5511583 prefixEnd_5511583 943363748716538213288399 := by
  unfold tailWord_5511583
  simp only [CollatzResearch.WordTrace]
  refine ⟨201023946791483569280515403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134015964527655712853676935 201023946791483569280515403)
  ·
    refine ⟨301535920187225353920773105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201023946791483569280515403 301535920187225353920773105)
    ·
      refine ⟨226151940140419015440579829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301535920187225353920773105 226151940140419015440579829)
      ·
        refine ⟨21201744388164282697554359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226151940140419015440579829 21201744388164282697554359)
        ·
          refine ⟨31802616582246424046331539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21201744388164282697554359 31802616582246424046331539)
          ·
            refine ⟨47703924873369636069497309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31802616582246424046331539 47703924873369636069497309)
            ·
              refine ⟨17888971827513613526061491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47703924873369636069497309 17888971827513613526061491)
              ·
                refine ⟨26833457741270420289092237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17888971827513613526061491 26833457741270420289092237)
                ·
                  refine ⟨10062546652976407608409589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26833457741270420289092237 10062546652976407608409589)
                  ·
                    refine ⟨943363748716538213288399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10062546652976407608409589 943363748716538213288399)
                    ·
                      rfl

theorem cell23_5511583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_5511583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511583 prefixEnd_5511583 := by exact prefixLift 5511583
  have htrace : WordTrace (prefixWord ++ tailWord_5511583) baseStart_5511583 baseEnd_5511583 := by
    simpa [prefixWord, tailWord_5511583, baseEnd_5511583] using wordTrace_append hprefix tailTrace_5511583
  have hstable : (prefixWord ++ tailWord_5511583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511583).length < 2 ^ (prefixWord ++ tailWord_5511583).sum := by decide
  have hdescent : baseEnd_5511583 < baseStart_5511583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511604 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 6]
def baseStart_5511604 : Nat := 118140960795 + 5511604 * 2 ^ 59
def prefixEnd_5511604 : Nat := 4983230072969 + 3 ^ 40 * 5511604 * 2
def baseEnd_5511604 : Nat := 314455781027039895300289

theorem tailTrace_5511604 : CollatzResearch.WordTrace tailWord_5511604 prefixEnd_5511604 314455781027039895300289 := by
  unfold tailWord_5511604
  simp only [CollatzResearch.WordTrace]
  refine ⟨100512356362203744933514933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134016475149604993244686577 100512356362203744933514933)
  ·
    refine ⟨9423033408956601087517025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100512356362203744933514933 9423033408956601087517025)
    ·
      refine ⟨7067275056717450815637769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9423033408956601087517025 7067275056717450815637769)
      ·
        refine ⟨5300456292538088111728327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7067275056717450815637769 5300456292538088111728327)
        ·
          refine ⟨7950684438807132167592491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300456292538088111728327 7950684438807132167592491)
          ·
            refine ⟨11926026658210698251388737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950684438807132167592491 11926026658210698251388737)
            ·
              refine ⟨8944519993658023688541553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11926026658210698251388737 8944519993658023688541553)
              ·
                refine ⟨6708389995243517766406165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8944519993658023688541553 6708389995243517766406165)
                ·
                  refine ⟨314455781027039895300289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6708389995243517766406165 314455781027039895300289)
                  ·
                    rfl

theorem cell23_5511604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_5511604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511604 prefixEnd_5511604 := by exact prefixLift 5511604
  have htrace : WordTrace (prefixWord ++ tailWord_5511604) baseStart_5511604 baseEnd_5511604 := by
    simpa [prefixWord, tailWord_5511604, baseEnd_5511604] using wordTrace_append hprefix tailTrace_5511604
  have hstable : (prefixWord ++ tailWord_5511604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511604).length < 2 ^ (prefixWord ++ tailWord_5511604).sum := by decide
  have hdescent : baseEnd_5511604 < baseStart_5511604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511637 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_5511637 : Nat := 118140960795 + 5511637 * 2 ^ 59
def prefixEnd_5511637 : Nat := 4983230072969 + 3 ^ 40 * 5511637 * 2
def baseEnd_5511637 : Nat := 2830118974104957428589949

theorem tailTrace_5511637 : CollatzResearch.WordTrace tailWord_5511637 prefixEnd_5511637 2830118974104957428589949 := by
  unfold tailWord_5511637
  simp only [CollatzResearch.WordTrace]
  refine ⟨201025916333287936502981165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134017277555525291001987443 201025916333287936502981165)
  ·
    refine ⟨75384718624982976188617937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201025916333287936502981165 75384718624982976188617937)
    ·
      refine ⟨56538538968737232141463453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75384718624982976188617937 56538538968737232141463453)
      ·
        refine ⟨21201952113276462053048795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56538538968737232141463453 21201952113276462053048795)
        ·
          refine ⟨31802928169914693079573193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21201952113276462053048795 31802928169914693079573193)
          ·
            refine ⟨23852196127436019809679895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31802928169914693079573193 23852196127436019809679895)
            ·
              refine ⟨35778294191154029714519843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23852196127436019809679895 35778294191154029714519843)
              ·
                refine ⟨53667441286731044571779765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35778294191154029714519843 53667441286731044571779765)
                ·
                  refine ⟨5031322620631035428604353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53667441286731044571779765 5031322620631035428604353)
                  ·
                    refine ⟨3773491965473276571453265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5031322620631035428604353 3773491965473276571453265)
                    ·
                      refine ⟨2830118974104957428589949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773491965473276571453265 2830118974104957428589949)
                      ·
                        rfl

theorem cell23_5511637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_5511637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511637 prefixEnd_5511637 := by exact prefixLift 5511637
  have htrace : WordTrace (prefixWord ++ tailWord_5511637) baseStart_5511637 baseEnd_5511637 := by
    simpa [prefixWord, tailWord_5511637, baseEnd_5511637] using wordTrace_append hprefix tailTrace_5511637
  have hstable : (prefixWord ++ tailWord_5511637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511637).length < 2 ^ (prefixWord ++ tailWord_5511637).sum := by decide
  have hdescent : baseEnd_5511637 < baseStart_5511637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511640 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_5511640 : Nat := 118140960795 + 5511640 * 2 ^ 59
def prefixEnd_5511640 : Nat := 4983230072969 + 3 ^ 40 * 5511640 * 2
def baseEnd_5511640 : Nat := 2830120514546920916852435

theorem tailTrace_5511640 : CollatzResearch.WordTrace tailWord_5511640 prefixEnd_5511640 2830120514546920916852435 := by
  unfold tailWord_5511640
  simp only [CollatzResearch.WordTrace]
  refine ⟨100513012876138534007670187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134017350501518045343560249 100513012876138534007670187)
  ·
    refine ⟨150769519314207801011505281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100513012876138534007670187 150769519314207801011505281)
    ·
      refine ⟨113077139485655850758628961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150769519314207801011505281 113077139485655850758628961)
      ·
        refine ⟨84807854614241888068971721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113077139485655850758628961 84807854614241888068971721)
        ·
          refine ⟨63605890960681416051728791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84807854614241888068971721 63605890960681416051728791)
          ·
            refine ⟨95408836441022124077593187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63605890960681416051728791 95408836441022124077593187)
            ·
              refine ⟨143113254661533186116389781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95408836441022124077593187 143113254661533186116389781)
              ·
                refine ⟨6708433812259368099205771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143113254661533186116389781 6708433812259368099205771)
                ·
                  refine ⟨10062650718389052148808657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6708433812259368099205771 10062650718389052148808657)
                  ·
                    refine ⟨7546988038791789111606493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10062650718389052148808657 7546988038791789111606493)
                    ·
                      refine ⟨2830120514546920916852435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7546988038791789111606493 2830120514546920916852435)
                      ·
                        rfl

theorem cell23_5511640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_5511640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511640 prefixEnd_5511640 := by exact prefixLift 5511640
  have htrace : WordTrace (prefixWord ++ tailWord_5511640) baseStart_5511640 baseEnd_5511640 := by
    simpa [prefixWord, tailWord_5511640, baseEnd_5511640] using wordTrace_append hprefix tailTrace_5511640
  have hstable : (prefixWord ++ tailWord_5511640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511640).length < 2 ^ (prefixWord ++ tailWord_5511640).sum := by decide
  have hdescent : baseEnd_5511640 < baseStart_5511640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511723 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 4]
def baseStart_5511723 : Nat := 118140960795 + 5511723 * 2 ^ 59
def prefixEnd_5511723 : Nat := 4983230072969 + 3 ^ 40 * 5511723 * 2
def baseEnd_5511723 : Nat := 2830163133441244092114553

theorem tailTrace_5511723 : CollatzResearch.WordTrace tailWord_5511723 prefixEnd_5511723 2830163133441244092114553 := by
  unfold tailWord_5511723
  simp only [CollatzResearch.WordTrace]
  refine ⟨201029053010976373190611823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134019368673984248793741215 201029053010976373190611823)
  ·
    refine ⟨301543579516464559785917735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201029053010976373190611823 301543579516464559785917735)
    ·
      refine ⟨452315369274696839678876603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301543579516464559785917735 452315369274696839678876603)
      ·
        refine ⟨678473053912045259518314905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452315369274696839678876603 678473053912045259518314905)
        ·
          refine ⟨508854790434033944638736179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 678473053912045259518314905 508854790434033944638736179)
          ·
            refine ⟨763282185651050916958104269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508854790434033944638736179 763282185651050916958104269)
            ·
              refine ⟨286230819619144093859289101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 763282185651050916958104269 286230819619144093859289101)
              ·
                refine ⟨107336557357179035197233413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286230819619144093859289101 107336557357179035197233413)
                ·
                  refine ⟨20125604504471069099481265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107336557357179035197233413 20125604504471069099481265)
                  ·
                    refine ⟨15094203378353301824610949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20125604504471069099481265 15094203378353301824610949)
                    ·
                      refine ⟨2830163133441244092114553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15094203378353301824610949 2830163133441244092114553)
                      ·
                        rfl

theorem cell23_5511723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 4].length) (baseStart_5511723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511723 prefixEnd_5511723 := by exact prefixLift 5511723
  have htrace : WordTrace (prefixWord ++ tailWord_5511723) baseStart_5511723 baseEnd_5511723 := by
    simpa [prefixWord, tailWord_5511723, baseEnd_5511723] using wordTrace_append hprefix tailTrace_5511723
  have hstable : (prefixWord ++ tailWord_5511723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511723).length < 2 ^ (prefixWord ++ tailWord_5511723).sum := by decide
  have hdescent : baseEnd_5511723 < baseStart_5511723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511748 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5511748 : Nat := 118140960795 + 5511748 * 2 ^ 59
def prefixEnd_5511748 : Nat := 4983230072969 + 3 ^ 40 * 5511748 * 2
def baseEnd_5511748 : Nat := 2830175970457606494301939

theorem tailTrace_5511748 : CollatzResearch.WordTrace tailWord_5511748 prefixEnd_5511748 2830175970457606494301939 := by
  unfold tailWord_5511748
  simp only [CollatzResearch.WordTrace]
  refine ⟨100514982417942901230135949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134019976557257201640181265 100514982417942901230135949)
  ·
    refine ⟨37693118406728587961300981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100514982417942901230135949 37693118406728587961300981)
    ·
      refine ⟨3533729850630805121371967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37693118406728587961300981 3533729850630805121371967)
      ·
        refine ⟨5300594775946207682057951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533729850630805121371967 5300594775946207682057951)
        ·
          refine ⟨7950892163919311523086927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300594775946207682057951 7950892163919311523086927)
          ·
            refine ⟨11926338245878967284630391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950892163919311523086927 11926338245878967284630391)
            ·
              refine ⟨17889507368818450926945587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11926338245878967284630391 17889507368818450926945587)
              ·
                refine ⟨26834261053227676390418381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17889507368818450926945587 26834261053227676390418381)
                ·
                  refine ⟨10062847894960378646406893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26834261053227676390418381 10062847894960378646406893)
                  ·
                    refine ⟨3773567960610141992402585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10062847894960378646406893 3773567960610141992402585)
                    ·
                      refine ⟨2830175970457606494301939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773567960610141992402585 2830175970457606494301939)
                      ·
                        rfl

theorem cell23_5511748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5511748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511748 prefixEnd_5511748 := by exact prefixLift 5511748
  have htrace : WordTrace (prefixWord ++ tailWord_5511748) baseStart_5511748 baseEnd_5511748 := by
    simpa [prefixWord, tailWord_5511748, baseEnd_5511748] using wordTrace_append hprefix tailTrace_5511748
  have hstable : (prefixWord ++ tailWord_5511748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511748).length < 2 ^ (prefixWord ++ tailWord_5511748).sum := by decide
  have hdescent : baseEnd_5511748 < baseStart_5511748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511780 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_5511780 : Nat := 118140960795 + 5511780 * 2 ^ 59
def prefixEnd_5511780 : Nat := 4983230072969 + 3 ^ 40 * 5511780 * 2
def baseEnd_5511780 : Nat := 943397467279516789700597

theorem tailTrace_5511780 : CollatzResearch.WordTrace tailWord_5511780 prefixEnd_5511780 943397467279516789700597 := by
  unfold tailWord_5511780
  simp only [CollatzResearch.WordTrace]
  refine ⟨100515565985884935962718397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134020754647846581283624529 100515565985884935962718397)
  ·
    refine ⟨37693337244706850986019399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100515565985884935962718397 37693337244706850986019399)
    ·
      refine ⟨56540005867060276479029099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37693337244706850986019399 56540005867060276479029099)
      ·
        refine ⟨84810008800590414718543649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56540005867060276479029099 84810008800590414718543649)
        ·
          refine ⟨63607506600442811038907737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84810008800590414718543649 63607506600442811038907737)
          ·
            refine ⟨47705629950332108279180803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63607506600442811038907737 47705629950332108279180803)
            ·
              refine ⟨71558444925498162418771205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47705629950332108279180803 71558444925498162418771205)
              ·
                refine ⟨13417208423530905453519601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71558444925498162418771205 13417208423530905453519601)
                ·
                  refine ⟨10062906317648179090139701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13417208423530905453519601 10062906317648179090139701)
                  ·
                    refine ⟨943397467279516789700597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10062906317648179090139701 943397467279516789700597)
                    ·
                      rfl

theorem cell23_5511780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_5511780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511780 prefixEnd_5511780 := by exact prefixLift 5511780
  have htrace : WordTrace (prefixWord ++ tailWord_5511780) baseStart_5511780 baseEnd_5511780 := by
    simpa [prefixWord, tailWord_5511780, baseEnd_5511780] using wordTrace_append hprefix tailTrace_5511780
  have hstable : (prefixWord ++ tailWord_5511780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511780).length < 2 ^ (prefixWord ++ tailWord_5511780).sum := by decide
  have hdescent : baseEnd_5511780 < baseStart_5511780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511784 : List Nat := [2, 1, 4, 3, 2, 1, 1, 4, 5]
def baseStart_5511784 : Nat := 118140960795 + 5511784 * 2 ^ 59
def prefixEnd_5511784 : Nat := 4983230072969 + 3 ^ 40 * 5511784 * 2
def baseEnd_5511784 : Nat := 314466050640129817050197

theorem tailTrace_5511784 : CollatzResearch.WordTrace tailWord_5511784 prefixEnd_5511784 314466050640129817050197 := by
  unfold tailWord_5511784
  simp only [CollatzResearch.WordTrace]
  refine ⟨100515638931877690304291203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134020851909170253739054937 100515638931877690304291203)
  ·
    refine ⟨150773458397816535456436805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100515638931877690304291203 150773458397816535456436805)
    ·
      refine ⟨28270023449590600398081901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150773458397816535456436805 28270023449590600398081901)
      ·
        refine ⟨10601258793596475149280713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28270023449590600398081901 10601258793596475149280713)
        ·
          refine ⟨7950944095197356361960535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10601258793596475149280713 7950944095197356361960535)
          ·
            refine ⟨11926416142796034542940803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950944095197356361960535 11926416142796034542940803)
            ·
              refine ⟨17889624214194051814411205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11926416142796034542940803 17889624214194051814411205)
              ·
                refine ⟨3354304540161384715202101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17889624214194051814411205 3354304540161384715202101)
                ·
                  refine ⟨314466050640129817050197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3354304540161384715202101 314466050640129817050197)
                  ·
                    rfl

theorem cell23_5511784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 5].length) (baseStart_5511784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511784 prefixEnd_5511784 := by exact prefixLift 5511784
  have htrace : WordTrace (prefixWord ++ tailWord_5511784) baseStart_5511784 baseEnd_5511784 := by
    simpa [prefixWord, tailWord_5511784, baseEnd_5511784] using wordTrace_append hprefix tailTrace_5511784
  have hstable : (prefixWord ++ tailWord_5511784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511784).length < 2 ^ (prefixWord ++ tailWord_5511784).sum := by decide
  have hdescent : baseEnd_5511784 < baseStart_5511784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511793 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 4, 8]
def baseStart_5511793 : Nat := 118140960795 + 5511793 * 2 ^ 59
def prefixEnd_5511793 : Nat := 4983230072969 + 3 ^ 40 * 5511793 * 2
def baseEnd_5511793 : Nat := 943399692362352939413077

theorem tailTrace_5511793 : CollatzResearch.WordTrace tailWord_5511793 prefixEnd_5511793 943399692362352939413077 := by
  unfold tailWord_5511793
  simp only [CollatzResearch.WordTrace]
  refine ⟨201031606120722775145660033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134021070747148516763773355 201031606120722775145660033)
  ·
    refine ⟨150773704590542081359245025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201031606120722775145660033 150773704590542081359245025)
    ·
      refine ⟨113080278442906561019433769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150773704590542081359245025 113080278442906561019433769)
      ·
        refine ⟨84810208832179920764575327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113080278442906561019433769 84810208832179920764575327)
        ·
          refine ⟨127215313248269881146862991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84810208832179920764575327 127215313248269881146862991)
          ·
            refine ⟨190822969872404821720294487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127215313248269881146862991 190822969872404821720294487)
            ·
              refine ⟨286234454808607232580441731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190822969872404821720294487 286234454808607232580441731)
              ·
                refine ⟨429351682212910848870662597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286234454808607232580441731 429351682212910848870662597)
                ·
                  refine ⟨80503440414920784163249237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 429351682212910848870662597 80503440414920784163249237)
                  ·
                    refine ⟨943399692362352939413077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80503440414920784163249237 943399692362352939413077)
                    ·
                      rfl

theorem cell23_5511793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_5511793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511793 prefixEnd_5511793 := by exact prefixLift 5511793
  have htrace : WordTrace (prefixWord ++ tailWord_5511793) baseStart_5511793 baseEnd_5511793 := by
    simpa [prefixWord, tailWord_5511793, baseEnd_5511793] using wordTrace_append hprefix tailTrace_5511793
  have hstable : (prefixWord ++ tailWord_5511793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511793).length < 2 ^ (prefixWord ++ tailWord_5511793).sum := by decide
  have hdescent : baseEnd_5511793 < baseStart_5511793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511823 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 10]
def baseStart_5511823 : Nat := 118140960795 + 5511823 * 2 ^ 59
def prefixEnd_5511823 : Nat := 4983230072969 + 3 ^ 40 * 5511823 * 2
def baseEnd_5511823 : Nat := 314468275722965966762677

theorem tailTrace_5511823 : CollatzResearch.WordTrace tailWord_5511823 prefixEnd_5511823 314468275722965966762677 := by
  unfold tailWord_5511823
  simp only [CollatzResearch.WordTrace]
  refine ⟨201032700310614090269252123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134021800207076060179501415 201032700310614090269252123)
  ·
    refine ⟨301549050465921135403878185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201032700310614090269252123 301549050465921135403878185)
    ·
      refine ⟨226161787849440851552908639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301549050465921135403878185 226161787849440851552908639)
      ·
        refine ⟨339242681774161277329362959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226161787849440851552908639 339242681774161277329362959)
        ·
          refine ⟨508864022661241915994044439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339242681774161277329362959 508864022661241915994044439)
          ·
            refine ⟨763296033991862873991066659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508864022661241915994044439 763296033991862873991066659)
            ·
              refine ⟨1144944050987794310986599989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763296033991862873991066659 1144944050987794310986599989)
              ·
                refine ⟨107338504780105716654993749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1144944050987794310986599989 107338504780105716654993749)
                ·
                  refine ⟨314468275722965966762677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 107338504780105716654993749 314468275722965966762677)
                  ·
                    rfl

theorem cell23_5511823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 10].length) (baseStart_5511823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511823 prefixEnd_5511823 := by exact prefixLift 5511823
  have htrace : WordTrace (prefixWord ++ tailWord_5511823) baseStart_5511823 baseEnd_5511823 := by
    simpa [prefixWord, tailWord_5511823, baseEnd_5511823] using wordTrace_append hprefix tailTrace_5511823
  have hstable : (prefixWord ++ tailWord_5511823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511823).length < 2 ^ (prefixWord ++ tailWord_5511823).sum := by decide
  have hdescent : baseEnd_5511823 < baseStart_5511823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511837 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_5511837 : Nat := 118140960795 + 5511837 * 2 ^ 59
def prefixEnd_5511837 : Nat := 4983230072969 + 3 ^ 40 * 5511837 * 2
def baseEnd_5511837 : Nat := 2830221670235856646089029

theorem tailTrace_5511837 : CollatzResearch.WordTrace tailWord_5511837 prefixEnd_5511837 2830221670235856646089029 := by
  unfold tailWord_5511837
  simp only [CollatzResearch.WordTrace]
  refine ⟨201033210932563370660261765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134022140621708913773507843 201033210932563370660261765)
  ·
    refine ⟨37693727049855631998799081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201033210932563370660261765 37693727049855631998799081)
    ·
      refine ⟨28270295287391723999099311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37693727049855631998799081 28270295287391723999099311)
      ·
        refine ⟨42405442931087585998648967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28270295287391723999099311 42405442931087585998648967)
        ·
          refine ⟨63608164396631378997973451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42405442931087585998648967 63608164396631378997973451)
          ·
            refine ⟨95412246594947068496960177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63608164396631378997973451 95412246594947068496960177)
            ·
              refine ⟨71559184946210301372720133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95412246594947068496960177 71559184946210301372720133)
              ·
                refine ⟨13417347177414431507385025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71559184946210301372720133 13417347177414431507385025)
                ·
                  refine ⟨10063010383060823630538769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13417347177414431507385025 10063010383060823630538769)
                  ·
                    refine ⟨7547257787295617722904077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10063010383060823630538769 7547257787295617722904077)
                    ·
                      refine ⟨2830221670235856646089029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7547257787295617722904077 2830221670235856646089029)
                      ·
                        rfl

theorem cell23_5511837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_5511837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511837 prefixEnd_5511837 := by exact prefixLift 5511837
  have htrace : WordTrace (prefixWord ++ tailWord_5511837) baseStart_5511837 baseEnd_5511837 := by
    simpa [prefixWord, tailWord_5511837, baseEnd_5511837] using wordTrace_append hprefix tailTrace_5511837
  have hstable : (prefixWord ++ tailWord_5511837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511837).length < 2 ^ (prefixWord ++ tailWord_5511837).sum := by decide
  have hdescent : baseEnd_5511837 < baseStart_5511837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511844 : List Nat := [2, 3, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_5511844 : Nat := 118140960795 + 5511844 * 2 ^ 59
def prefixEnd_5511844 : Nat := 4983230072969 + 3 ^ 40 * 5511844 * 2
def baseEnd_5511844 : Nat := 943408421533479372900499

theorem tailTrace_5511844 : CollatzResearch.WordTrace tailWord_5511844 prefixEnd_5511844 943408421533479372900499 := by
  unfold tailWord_5511844
  simp only [CollatzResearch.WordTrace]
  refine ⟨100516733121769005427883293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134022310829025340570511057 100516733121769005427883293)
  ·
    refine ⟨37693774920663377035456235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100516733121769005427883293 37693774920663377035456235)
    ·
      refine ⟨56540662380995065553184353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37693774920663377035456235 56540662380995065553184353)
      ·
        refine ⟨42405496785746299164888265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56540662380995065553184353 42405496785746299164888265)
        ·
          refine ⟨31804122589309724373666199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42405496785746299164888265 31804122589309724373666199)
          ·
            refine ⟨47706183883964586560499299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31804122589309724373666199 47706183883964586560499299)
            ·
              refine ⟨71559275825946879840748949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47706183883964586560499299 71559275825946879840748949)
              ·
                refine ⟨3354341054341259992535107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71559275825946879840748949 3354341054341259992535107)
                ·
                  refine ⟨5031511581511889988802661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354341054341259992535107 5031511581511889988802661)
                  ·
                    refine ⟨943408421533479372900499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5031511581511889988802661 943408421533479372900499)
                    ·
                      rfl

theorem cell23_5511844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_5511844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511844 prefixEnd_5511844 := by exact prefixLift 5511844
  have htrace : WordTrace (prefixWord ++ tailWord_5511844) baseStart_5511844 baseEnd_5511844 := by
    simpa [prefixWord, tailWord_5511844, baseEnd_5511844] using wordTrace_append hprefix tailTrace_5511844
  have hstable : (prefixWord ++ tailWord_5511844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511844).length < 2 ^ (prefixWord ++ tailWord_5511844).sum := by decide
  have hdescent : baseEnd_5511844 < baseStart_5511844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511854 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5511854 : Nat := 118140960795 + 5511854 * 2 ^ 59
def prefixEnd_5511854 : Nat := 4983230072969 + 3 ^ 40 * 5511854 * 2
def baseEnd_5511854 : Nat := 2830230399406983079576451

theorem tailTrace_5511854 : CollatzResearch.WordTrace tailWord_5511854 prefixEnd_5511854 2830230399406983079576451 := by
  unfold tailWord_5511854
  simp only [CollatzResearch.WordTrace]
  refine ⟨25129228871687722820453827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134022553982334521709087077 25129228871687722820453827)
  ·
    refine ⟨37693843307531584230680741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25129228871687722820453827 37693843307531584230680741)
    ·
      refine ⟨7067595620162172043252639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37693843307531584230680741 7067595620162172043252639)
      ·
        refine ⟨10601393430243258064878959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7067595620162172043252639 10601393430243258064878959)
        ·
          refine ⟨15902090145364887097318439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10601393430243258064878959 15902090145364887097318439)
          ·
            refine ⟨23853135218047330645977659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15902090145364887097318439 23853135218047330645977659)
            ·
              refine ⟨35779702827070995968966489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23853135218047330645977659 35779702827070995968966489)
              ·
                refine ⟨26834777120303246976724867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35779702827070995968966489 26834777120303246976724867)
                ·
                  refine ⟨40252165680454870465087301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26834777120303246976724867 40252165680454870465087301)
                  ·
                    refine ⟨7547281065085288212203869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40252165680454870465087301 7547281065085288212203869)
                    ·
                      refine ⟨2830230399406983079576451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7547281065085288212203869 2830230399406983079576451)
                      ·
                        rfl

theorem cell23_5511854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5511854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511854 prefixEnd_5511854 := by exact prefixLift 5511854
  have htrace : WordTrace (prefixWord ++ tailWord_5511854) baseStart_5511854 baseEnd_5511854 := by
    simpa [prefixWord, tailWord_5511854, baseEnd_5511854] using wordTrace_append hprefix tailTrace_5511854
  have hstable : (prefixWord ++ tailWord_5511854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511854).length < 2 ^ (prefixWord ++ tailWord_5511854).sum := by decide
  have hdescent : baseEnd_5511854 < baseStart_5511854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511917 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_5511917 : Nat := 118140960795 + 5511917 * 2 ^ 59
def prefixEnd_5511917 : Nat := 4983230072969 + 3 ^ 40 * 5511917 * 2
def baseEnd_5511917 : Nat := 943420916229405444362887

theorem tailTrace_5511917 : CollatzResearch.WordTrace tailWord_5511917 prefixEnd_5511917 943420916229405444362887 := by
  unfold tailWord_5511917
  simp only [CollatzResearch.WordTrace]
  refine ⟨201036128772273544323174005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134024085848182362882116003 201036128772273544323174005)
  ·
    refine ⟨18847137072400644780297563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201036128772273544323174005 18847137072400644780297563)
    ·
      refine ⟨28270705608600967170446345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18847137072400644780297563 28270705608600967170446345)
      ·
        refine ⟨21203029206450725377834759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28270705608600967170446345 21203029206450725377834759)
        ·
          refine ⟨31804543809676088066752139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21203029206450725377834759 31804543809676088066752139)
          ·
            refine ⟨47706815714514132100128209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31804543809676088066752139 47706815714514132100128209)
            ·
              refine ⟨35780111785885599075096157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47706815714514132100128209 35780111785885599075096157)
              ·
                refine ⟨13417541919707099653161059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35780111785885599075096157 13417541919707099653161059)
                ·
                  refine ⟨20126312879560649479741589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13417541919707099653161059 20126312879560649479741589)
                  ·
                    refine ⟨943420916229405444362887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20126312879560649479741589 943420916229405444362887)
                    ·
                      rfl

theorem cell23_5511917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_5511917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511917 prefixEnd_5511917 := by exact prefixLift 5511917
  have htrace : WordTrace (prefixWord ++ tailWord_5511917) baseStart_5511917 baseEnd_5511917 := by
    simpa [prefixWord, tailWord_5511917, baseEnd_5511917] using wordTrace_append hprefix tailTrace_5511917
  have hstable : (prefixWord ++ tailWord_5511917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511917).length < 2 ^ (prefixWord ++ tailWord_5511917).sum := by decide
  have hdescent : baseEnd_5511917 < baseStart_5511917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511920 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_5511920 : Nat := 118140960795 + 5511920 * 2 ^ 59
def prefixEnd_5511920 : Nat := 4983230072969 + 3 ^ 40 * 5511920 * 2
def baseEnd_5511920 : Nat := 2830264289130179821351147

theorem tailTrace_5511920 : CollatzResearch.WordTrace tailWord_5511920 prefixEnd_5511920 2830264289130179821351147 := by
  unfold tailWord_5511920
  simp only [CollatzResearch.WordTrace]
  refine ⟨100518119095631337917766607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134024158794175117223688809 100518119095631337917766607)
  ·
    refine ⟨150777178643447006876649911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100518119095631337917766607 150777178643447006876649911)
    ·
      refine ⟨226165767965170510314974867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150777178643447006876649911 226165767965170510314974867)
      ·
        refine ⟨339248651947755765472462301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226165767965170510314974867 339248651947755765472462301)
        ·
          refine ⟨127218244480408412052173363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339248651947755765472462301 127218244480408412052173363)
          ·
            refine ⟨190827366720612618078260045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127218244480408412052173363 190827366720612618078260045)
            ·
              refine ⟨71560262520229731779347517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190827366720612618078260045 71560262520229731779347517)
              ·
                refine ⟨26835098445086149417255319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71560262520229731779347517 26835098445086149417255319)
                ·
                  refine ⟨40252647667629224125882979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26835098445086149417255319 40252647667629224125882979)
                  ·
                    refine ⟨60378971501443836188824469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40252647667629224125882979 60378971501443836188824469)
                    ·
                      refine ⟨2830264289130179821351147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60378971501443836188824469 2830264289130179821351147)
                      ·
                        rfl

theorem cell23_5511920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_5511920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511920 prefixEnd_5511920 := by exact prefixLift 5511920
  have htrace : WordTrace (prefixWord ++ tailWord_5511920) baseStart_5511920 baseEnd_5511920 := by
    simpa [prefixWord, tailWord_5511920, baseEnd_5511920] using wordTrace_append hprefix tailTrace_5511920
  have hstable : (prefixWord ++ tailWord_5511920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511920).length < 2 ^ (prefixWord ++ tailWord_5511920).sum := by decide
  have hdescent : baseEnd_5511920 < baseStart_5511920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511930 : List Nat := [3, 1, 1, 1, 1, 3, 4, 9]
def baseStart_5511930 : Nat := 118140960795 + 5511930 * 2 ^ 59
def prefixEnd_5511930 : Nat := 4983230072969 + 3 ^ 40 * 5511930 * 2
def baseEnd_5511930 : Nat := 104824793479137954897263

theorem tailTrace_5511930 : CollatzResearch.WordTrace tailWord_5511930 prefixEnd_5511930 104824793479137954897263 := by
  unfold tailWord_5511930
  simp only [CollatzResearch.WordTrace]
  refine ⟨50259150730306611885849311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134024401947484298362264829 50259150730306611885849311)
  ·
    refine ⟨75388726095459917828773967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50259150730306611885849311 75388726095459917828773967)
    ·
      refine ⟨113083089143189876743160951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75388726095459917828773967 113083089143189876743160951)
      ·
        refine ⟨169624633714784815114741427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113083089143189876743160951 169624633714784815114741427)
        ·
          refine ⟨254436950572177222672112141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169624633714784815114741427 254436950572177222672112141)
          ·
            refine ⟨95413856464566458502042053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254436950572177222672112141 95413856464566458502042053)
            ·
              refine ⟨17890098087106210969132885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95413856464566458502042053 17890098087106210969132885)
              ·
                refine ⟨104824793479137954897263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17890098087106210969132885 104824793479137954897263)
                ·
                  rfl

theorem cell23_5511930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 9].length) (baseStart_5511930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511930 prefixEnd_5511930 := by exact prefixLift 5511930
  have htrace : WordTrace (prefixWord ++ tailWord_5511930) baseStart_5511930 baseEnd_5511930 := by
    simpa [prefixWord, tailWord_5511930, baseEnd_5511930] using wordTrace_append hprefix tailTrace_5511930
  have hstable : (prefixWord ++ tailWord_5511930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511930).length < 2 ^ (prefixWord ++ tailWord_5511930).sum := by decide
  have hdescent : baseEnd_5511930 < baseStart_5511930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511934 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_5511934 : Nat := 118140960795 + 5511934 * 2 ^ 59
def prefixEnd_5511934 : Nat := 4983230072969 + 3 ^ 40 * 5511934 * 2
def baseEnd_5511934 : Nat := 943423825953114255525361

theorem tailTrace_5511934 : CollatzResearch.WordTrace tailWord_5511934 prefixEnd_5511934 943423825953114255525361 := by
  unfold tailWord_5511934
  simp only [CollatzResearch.WordTrace]
  refine ⟨25129593601651494528317857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134024499208807970817695237 25129593601651494528317857)
  ·
    refine ⟨18847195201238620896238393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25129593601651494528317857 18847195201238620896238393)
    ·
      refine ⟨14135396400928965672178795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18847195201238620896238393 14135396400928965672178795)
      ·
        refine ⟨21203094601393448508268193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14135396400928965672178795 21203094601393448508268193)
        ·
          refine ⟨15902320951045086381201145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21203094601393448508268193 15902320951045086381201145)
          ·
            refine ⟨11926740713283814785900859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15902320951045086381201145 11926740713283814785900859)
            ·
              refine ⟨17890111069925722178851289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11926740713283814785900859 17890111069925722178851289)
              ·
                refine ⟨13417583302444291634138467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17890111069925722178851289 13417583302444291634138467)
                ·
                  refine ⟨20126374953666437451207701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13417583302444291634138467 20126374953666437451207701)
                  ·
                    refine ⟨943423825953114255525361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20126374953666437451207701 943423825953114255525361)
                    ·
                      rfl

theorem cell23_5511934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_5511934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511934 prefixEnd_5511934 := by exact prefixLift 5511934
  have htrace : WordTrace (prefixWord ++ tailWord_5511934) baseStart_5511934 baseEnd_5511934 := by
    simpa [prefixWord, tailWord_5511934, baseEnd_5511934] using wordTrace_append hprefix tailTrace_5511934
  have hstable : (prefixWord ++ tailWord_5511934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511934).length < 2 ^ (prefixWord ++ tailWord_5511934).sum := by decide
  have hdescent : baseEnd_5511934 < baseStart_5511934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511944 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_5511944 : Nat := 118140960795 + 5511944 * 2 ^ 59
def prefixEnd_5511944 : Nat := 4983230072969 + 3 ^ 40 * 5511944 * 2
def baseEnd_5511944 : Nat := 2830276612665887727451037

theorem tailTrace_5511944 : CollatzResearch.WordTrace tailWord_5511944 prefixEnd_5511944 2830276612665887727451037 := by
  unfold tailWord_5511944
  simp only [CollatzResearch.WordTrace]
  refine ⟨100518556771587863967203443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134024742362117151956271257 100518556771587863967203443)
  ·
    refine ⟨150777835157381795950805165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100518556771587863967203443 150777835157381795950805165)
    ·
      refine ⟨56541688184018173481551937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150777835157381795950805165 56541688184018173481551937)
      ·
        refine ⟨42406266138013630111163953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56541688184018173481551937 42406266138013630111163953)
        ·
          refine ⟨31804699603510222583372965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42406266138013630111163953 31804699603510222583372965)
          ·
            refine ⟨5963381175658166734382431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31804699603510222583372965 5963381175658166734382431)
            ·
              refine ⟨8945071763487250101573647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5963381175658166734382431 8945071763487250101573647)
              ·
                refine ⟨13417607645230875152360471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8945071763487250101573647 13417607645230875152360471)
                ·
                  refine ⟨20126411467846312728540707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13417607645230875152360471 20126411467846312728540707)
                  ·
                    refine ⟨30189617201769469092811061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20126411467846312728540707 30189617201769469092811061)
                    ·
                      refine ⟨2830276612665887727451037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30189617201769469092811061 2830276612665887727451037)
                      ·
                        rfl

theorem cell23_5511944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_5511944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511944 prefixEnd_5511944 := by exact prefixLift 5511944
  have htrace : WordTrace (prefixWord ++ tailWord_5511944) baseStart_5511944 baseEnd_5511944 := by
    simpa [prefixWord, tailWord_5511944, baseEnd_5511944] using wordTrace_append hprefix tailTrace_5511944
  have hstable : (prefixWord ++ tailWord_5511944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511944).length < 2 ^ (prefixWord ++ tailWord_5511944).sum := by decide
  have hdescent : baseEnd_5511944 < baseStart_5511944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5511957 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_5511957 : Nat := 118140960795 + 5511957 * 2 ^ 59
def prefixEnd_5511957 : Nat := 4983230072969 + 3 ^ 40 * 5511957 * 2
def baseEnd_5511957 : Nat := 2830283287914396176588477

theorem tailTrace_5511957 : CollatzResearch.WordTrace tailWord_5511957 prefixEnd_5511957 2830283287914396176588477 := by
  unfold tailWord_5511957
  simp only [CollatzResearch.WordTrace]
  refine ⟨201037587692128631154630125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134025058461419087436420083 201037587692128631154630125)
  ·
    refine ⟨75389095384548236682986297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201037587692128631154630125 75389095384548236682986297)
    ·
      refine ⟨56541821538411177512239723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75389095384548236682986297 56541821538411177512239723)
      ·
        refine ⟨84812732307616766268359585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56541821538411177512239723 84812732307616766268359585)
        ·
          refine ⟨63609549230712574701269689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84812732307616766268359585 63609549230712574701269689)
          ·
            refine ⟨47707161923034431025952267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63609549230712574701269689 47707161923034431025952267)
            ·
              refine ⟨71560742884551646538928401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47707161923034431025952267 71560742884551646538928401)
              ·
                refine ⟨53670557163413734904196301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71560742884551646538928401 53670557163413734904196301)
                ·
                  refine ⟨20126458936280150589073613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53670557163413734904196301 20126458936280150589073613)
                  ·
                    refine ⟨7547422101105056470902605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20126458936280150589073613 7547422101105056470902605)
                    ·
                      refine ⟨2830283287914396176588477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7547422101105056470902605 2830283287914396176588477)
                      ·
                        rfl

theorem cell23_5511957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_5511957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5511957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5511957 prefixEnd_5511957 := by exact prefixLift 5511957
  have htrace : WordTrace (prefixWord ++ tailWord_5511957) baseStart_5511957 baseEnd_5511957 := by
    simpa [prefixWord, tailWord_5511957, baseEnd_5511957] using wordTrace_append hprefix tailTrace_5511957
  have hstable : (prefixWord ++ tailWord_5511957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5511957).length < 2 ^ (prefixWord ++ tailWord_5511957).sum := by decide
  have hdescent : baseEnd_5511957 < baseStart_5511957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5511957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512014 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_5512014 : Nat := 118140960795 + 5512014 * 2 ^ 59
def prefixEnd_5512014 : Nat := 4983230072969 + 3 ^ 40 * 5512014 * 2
def baseEnd_5512014 : Nat := 2830312556311702453575715

theorem tailTrace_5512014 : CollatzResearch.WordTrace tailWord_5512014 prefixEnd_5512014 2830312556311702453575715 := by
  unfold tailWord_5512014
  simp only [CollatzResearch.WordTrace]
  refine ⟨25129958331615266236181887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134026444435281419926303397 25129958331615266236181887)
  ·
    refine ⟨37694937497422899354272831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25129958331615266236181887 37694937497422899354272831)
    ·
      refine ⟨56542406246134349031409247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37694937497422899354272831 56542406246134349031409247)
      ·
        refine ⟨84813609369201523547113871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56542406246134349031409247 84813609369201523547113871)
        ·
          refine ⟨127220414053802285320670807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84813609369201523547113871 127220414053802285320670807)
          ·
            refine ⟨190830621080703427981006211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127220414053802285320670807 190830621080703427981006211)
            ·
              refine ⟨286245931621055141971509317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190830621080703427981006211 286245931621055141971509317)
              ·
                refine ⟨53671112178947839119657997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286245931621055141971509317 53671112178947839119657997)
                ·
                  refine ⟨20126667067105439669871749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53671112178947839119657997 20126667067105439669871749)
                  ·
                    refine ⟨3773750075082269938100953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20126667067105439669871749 3773750075082269938100953)
                    ·
                      refine ⟨2830312556311702453575715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773750075082269938100953 2830312556311702453575715)
                      ·
                        rfl

theorem cell23_5512014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_5512014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512014 prefixEnd_5512014 := by exact prefixLift 5512014
  have htrace : WordTrace (prefixWord ++ tailWord_5512014) baseStart_5512014 baseEnd_5512014 := by
    simpa [prefixWord, tailWord_5512014, baseEnd_5512014] using wordTrace_append hprefix tailTrace_5512014
  have hstable : (prefixWord ++ tailWord_5512014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512014).length < 2 ^ (prefixWord ++ tailWord_5512014).sum := by decide
  have hdescent : baseEnd_5512014 < baseStart_5512014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512037 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 7]
def baseStart_5512037 : Nat := 118140960795 + 5512037 * 2 ^ 59
def prefixEnd_5512037 : Nat := 4983230072969 + 3 ^ 40 * 5512037 * 2
def baseEnd_5512037 : Nat := 314480485151861762620901

theorem tailTrace_5512037 : CollatzResearch.WordTrace tailWord_5512037 prefixEnd_5512037 314480485151861762620901 := by
  unfold tailWord_5512037
  simp only [CollatzResearch.WordTrace]
  refine ⟨201040505531838804817542365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134027003687892536545028243 201040505531838804817542365)
  ·
    refine ⟨75390189574439551806578387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201040505531838804817542365 75390189574439551806578387)
    ·
      refine ⟨113085284361659327709867581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75390189574439551806578387 113085284361659327709867581)
      ·
        refine ⟨42406981635622247891200343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113085284361659327709867581 42406981635622247891200343)
        ·
          refine ⟨63610472453433371836800515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42406981635622247891200343 63610472453433371836800515)
          ·
            refine ⟨95415708680150057755200773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63610472453433371836800515 95415708680150057755200773)
            ·
              refine ⟨17890445377528135829100145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95415708680150057755200773 17890445377528135829100145)
              ·
                refine ⟨13417834033146101871825109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17890445377528135829100145 13417834033146101871825109)
                ·
                  refine ⟨314480485151861762620901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13417834033146101871825109 314480485151861762620901)
                  ·
                    rfl

theorem cell23_5512037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_5512037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512037 prefixEnd_5512037 := by exact prefixLift 5512037
  have htrace : WordTrace (prefixWord ++ tailWord_5512037) baseStart_5512037 baseEnd_5512037 := by
    simpa [prefixWord, tailWord_5512037, baseEnd_5512037] using wordTrace_append hprefix tailTrace_5512037
  have hstable : (prefixWord ++ tailWord_5512037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512037).length < 2 ^ (prefixWord ++ tailWord_5512037).sum := by decide
  have hdescent : baseEnd_5512037 < baseStart_5512037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512047 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 3]
def baseStart_5512047 : Nat := 118140960795 + 5512047 * 2 ^ 59
def prefixEnd_5512047 : Nat := 4983230072969 + 3 ^ 40 * 5512047 * 2
def baseEnd_5512047 : Nat := 2830329501173300824463063

theorem tailTrace_5512047 : CollatzResearch.WordTrace tailWord_5512047 prefixEnd_5512047 2830329501173300824463063 := by
  unfold tailWord_5512047
  simp only [CollatzResearch.WordTrace]
  refine ⟨201040870261802576525406395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134027246841201717683604263 201040870261802576525406395)
  ·
    refine ⟨301561305392703864788109593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201040870261802576525406395 301561305392703864788109593)
    ·
      refine ⟨226170979044527898591082195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301561305392703864788109593 226170979044527898591082195)
      ·
        refine ⟨339256468566791847886623293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226170979044527898591082195 339256468566791847886623293)
        ·
          refine ⟨127221175712546942957483735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339256468566791847886623293 127221175712546942957483735)
          ·
            refine ⟨190831763568820414436225603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127221175712546942957483735 190831763568820414436225603)
            ·
              refine ⟨286247645353230621654338405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190831763568820414436225603 286247645353230621654338405)
              ·
                refine ⟨53671433503730741560188451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286247645353230621654338405 53671433503730741560188451)
                ·
                  refine ⟨80507150255596112340282677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53671433503730741560188451 80507150255596112340282677)
                  ·
                    refine ⟨7547545336462135531901501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80507150255596112340282677 7547545336462135531901501)
                    ·
                      refine ⟨2830329501173300824463063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7547545336462135531901501 2830329501173300824463063)
                      ·
                        rfl

theorem cell23_5512047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_5512047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512047 prefixEnd_5512047 := by exact prefixLift 5512047
  have htrace : WordTrace (prefixWord ++ tailWord_5512047) baseStart_5512047 baseEnd_5512047 := by
    simpa [prefixWord, tailWord_5512047, baseEnd_5512047] using wordTrace_append hprefix tailTrace_5512047
  have hstable : (prefixWord ++ tailWord_5512047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512047).length < 2 ^ (prefixWord ++ tailWord_5512047).sum := by decide
  have hdescent : baseEnd_5512047 < baseStart_5512047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512084 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_5512084 : Nat := 118140960795 + 5512084 * 2 ^ 59
def prefixEnd_5512084 : Nat := 4983230072969 + 3 ^ 40 * 5512084 * 2
def baseEnd_5512084 : Nat := 943449499985839059900131

theorem tailTrace_5512084 : CollatzResearch.WordTrace tailWord_5512084 prefixEnd_5512084 943449499985839059900131 := by
  unfold tailWord_5512084
  simp only [CollatzResearch.WordTrace]
  refine ⟨100521109881334265922251653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134028146508445687896335537 100521109881334265922251653)
  ·
    refine ⟨18847708102750174860422185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100521109881334265922251653 18847708102750174860422185)
    ·
      refine ⟨14135781077062631145316639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18847708102750174860422185 14135781077062631145316639)
      ·
        refine ⟨21203671615593946717974959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14135781077062631145316639 21203671615593946717974959)
        ·
          refine ⟨31805507423390920076962439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21203671615593946717974959 31805507423390920076962439)
          ·
            refine ⟨47708261135086380115443659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31805507423390920076962439 47708261135086380115443659)
            ·
              refine ⟨71562391702629570173165489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47708261135086380115443659 71562391702629570173165489)
              ·
                refine ⟨53671793776972177629874117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71562391702629570173165489 53671793776972177629874117)
                ·
                  refine ⟨10063461333182283305601397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53671793776972177629874117 10063461333182283305601397)
                  ·
                    refine ⟨943449499985839059900131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10063461333182283305601397 943449499985839059900131)
                    ·
                      rfl

theorem cell23_5512084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_5512084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512084 prefixEnd_5512084 := by exact prefixLift 5512084
  have htrace : WordTrace (prefixWord ++ tailWord_5512084) baseStart_5512084 baseEnd_5512084 := by
    simpa [prefixWord, tailWord_5512084, baseEnd_5512084] using wordTrace_append hprefix tailTrace_5512084
  have hstable : (prefixWord ++ tailWord_5512084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512084).length < 2 ^ (prefixWord ++ tailWord_5512084).sum := by decide
  have hdescent : baseEnd_5512084 < baseStart_5512084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512131 : List Nat := [1, 1, 1, 3, 1, 1, 2, 8, 1, 4]
def baseStart_5512131 : Nat := 118140960795 + 5512131 * 2 ^ 59
def prefixEnd_5512131 : Nat := 4983230072969 + 3 ^ 40 * 5512131 * 2
def baseEnd_5512131 : Nat := 943457544516092831937559

theorem tailTrace_5512131 : CollatzResearch.WordTrace tailWord_5512131 prefixEnd_5512131 943457544516092831937559 := by
  unfold tailWord_5512131
  simp only [CollatzResearch.WordTrace]
  refine ⟨201043933993498258871464247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134029289328998839247642831 201043933993498258871464247)
  ·
    refine ⟨301565900990247388307196371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201043933993498258871464247 301565900990247388307196371)
    ·
      refine ⟨452348851485371082460794557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301565900990247388307196371 452348851485371082460794557)
      ·
        refine ⟨169630819307014155922797959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 452348851485371082460794557 169630819307014155922797959)
        ·
          refine ⟨254446228960521233884196939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169630819307014155922797959 254446228960521233884196939)
          ·
            refine ⟨381669343440781850826295409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254446228960521233884196939 381669343440781850826295409)
            ·
              refine ⟨286252007580586388119721557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381669343440781850826295409 286252007580586388119721557)
              ·
                refine ⟨3354515713834996735777987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 286252007580586388119721557 3354515713834996735777987)
                ·
                  refine ⟨5031773570752495103666981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354515713834996735777987 5031773570752495103666981)
                  ·
                    refine ⟨943457544516092831937559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5031773570752495103666981 943457544516092831937559)
                    ·
                      rfl

theorem cell23_5512131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 4].length) (baseStart_5512131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512131 prefixEnd_5512131 := by exact prefixLift 5512131
  have htrace : WordTrace (prefixWord ++ tailWord_5512131) baseStart_5512131 baseEnd_5512131 := by
    simpa [prefixWord, tailWord_5512131, baseEnd_5512131] using wordTrace_append hprefix tailTrace_5512131
  have hstable : (prefixWord ++ tailWord_5512131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512131).length < 2 ^ (prefixWord ++ tailWord_5512131).sum := by decide
  have hdescent : baseEnd_5512131 < baseStart_5512131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512188 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_5512188 : Nat := 118140960795 + 5512188 * 2 ^ 59
def prefixEnd_5512188 : Nat := 4983230072969 + 3 ^ 40 * 5512188 * 2
def baseEnd_5512188 : Nat := 2830401901945584772799915

theorem tailTrace_5512188 : CollatzResearch.WordTrace tailWord_5512188 prefixEnd_5512188 2830401901945584772799915 := by
  unfold tailWord_5512188
  simp only [CollatzResearch.WordTrace]
  refine ⟨100523006477145878803144609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134030675302861171737526145 100523006477145878803144609)
  ·
    refine ⟨75392254857859409102358457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100523006477145878803144609 75392254857859409102358457)
    ·
      refine ⟨56544191143394556826768843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75392254857859409102358457 56544191143394556826768843)
      ·
        refine ⟨84816286715091835240153265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56544191143394556826768843 84816286715091835240153265)
        ·
          refine ⟨63612215036318876430114949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84816286715091835240153265 63612215036318876430114949)
          ·
            refine ⟨11927290319309789330646553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63612215036318876430114949 11927290319309789330646553)
            ·
              refine ⟨8945467739482341997984915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11927290319309789330646553 8945467739482341997984915)
              ·
                refine ⟨13418201609223512996977373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8945467739482341997984915 13418201609223512996977373)
                ·
                  refine ⟨5031825603458817373866515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13418201609223512996977373 5031825603458817373866515)
                  ·
                    refine ⟨7547738405188226060799773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031825603458817373866515 7547738405188226060799773)
                    ·
                      refine ⟨2830401901945584772799915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7547738405188226060799773 2830401901945584772799915)
                      ·
                        rfl

theorem cell23_5512188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_5512188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512188 prefixEnd_5512188 := by exact prefixLift 5512188
  have htrace : WordTrace (prefixWord ++ tailWord_5512188) baseStart_5512188 baseEnd_5512188 := by
    simpa [prefixWord, tailWord_5512188, baseEnd_5512188] using wordTrace_append hprefix tailTrace_5512188
  have hstable : (prefixWord ++ tailWord_5512188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512188).length < 2 ^ (prefixWord ++ tailWord_5512188).sum := by decide
  have hdescent : baseEnd_5512188 < baseStart_5512188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512228 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_5512228 : Nat := 118140960795 + 5512228 * 2 ^ 59
def prefixEnd_5512228 : Nat := 4983230072969 + 3 ^ 40 * 5512228 * 2
def baseEnd_5512228 : Nat := 2830422441171764616299731

theorem tailTrace_5512228 : CollatzResearch.WordTrace tailWord_5512228 prefixEnd_5512228 2830422441171764616299731 := by
  unfold tailWord_5512228
  simp only [CollatzResearch.WordTrace]
  refine ⟨100523735937073422218872669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134031647916097896291830225 100523735937073422218872669)
  ·
    refine ⟨37696400976402533332077251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100523735937073422218872669 37696400976402533332077251)
    ·
      refine ⟨56544601464603799998115877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37696400976402533332077251 56544601464603799998115877)
      ·
        refine ⟨10602112774613212499646727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56544601464603799998115877 10602112774613212499646727)
        ·
          refine ⟨15903169161919818749470091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10602112774613212499646727 15903169161919818749470091)
          ·
            refine ⟨23854753742879728124205137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15903169161919818749470091 23854753742879728124205137)
            ·
              refine ⟨17891065307159796093153853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23854753742879728124205137 17891065307159796093153853)
              ·
                refine ⟨6709149490184923534932695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17891065307159796093153853 6709149490184923534932695)
                ·
                  refine ⟨10063724235277385302399043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6709149490184923534932695 10063724235277385302399043)
                  ·
                    refine ⟨15095586352916077953598565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10063724235277385302399043 15095586352916077953598565)
                    ·
                      refine ⟨2830422441171764616299731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15095586352916077953598565 2830422441171764616299731)
                      ·
                        rfl

theorem cell23_5512228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_5512228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512228 prefixEnd_5512228 := by exact prefixLift 5512228
  have htrace : WordTrace (prefixWord ++ tailWord_5512228) baseStart_5512228 baseEnd_5512228 := by
    simpa [prefixWord, tailWord_5512228, baseEnd_5512228] using wordTrace_append hprefix tailTrace_5512228
  have hstable : (prefixWord ++ tailWord_5512228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512228).length < 2 ^ (prefixWord ++ tailWord_5512228).sum := by decide
  have hdescent : baseEnd_5512228 < baseStart_5512228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512238 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_5512238 : Nat := 118140960795 + 5512238 * 2 ^ 59
def prefixEnd_5512238 : Nat := 4983230072969 + 3 ^ 40 * 5512238 * 2
def baseEnd_5512238 : Nat := 943475858659436525724895

theorem tailTrace_5512238 : CollatzResearch.WordTrace tailWord_5512238 prefixEnd_5512238 943475858659436525724895 := by
  unfold tailWord_5512238
  simp only [CollatzResearch.WordTrace]
  refine ⟨25130979575513827018201171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134031891069407077430406245 25130979575513827018201171)
  ·
    refine ⟨37696469363270740527301757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25130979575513827018201171 37696469363270740527301757)
    ·
      refine ⟨14136176011226527697738159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37696469363270740527301757 14136176011226527697738159)
      ·
        refine ⟨21204264016839791546607239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14136176011226527697738159 21204264016839791546607239)
        ·
          refine ⟨31806396025259687319910859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21204264016839791546607239 31806396025259687319910859)
          ·
            refine ⟨47709594037889530979866289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31806396025259687319910859 47709594037889530979866289)
            ·
              refine ⟨35782195528417148234899717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47709594037889530979866289 35782195528417148234899717)
              ·
                refine ⟨6709161661578215294043697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35782195528417148234899717 6709161661578215294043697)
                ·
                  refine ⟨5031871246183661470532773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6709161661578215294043697 5031871246183661470532773)
                  ·
                    refine ⟨943475858659436525724895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5031871246183661470532773 943475858659436525724895)
                    ·
                      rfl

theorem cell23_5512238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_5512238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512238 prefixEnd_5512238 := by exact prefixLift 5512238
  have htrace : WordTrace (prefixWord ++ tailWord_5512238) baseStart_5512238 baseEnd_5512238 := by
    simpa [prefixWord, tailWord_5512238, baseEnd_5512238] using wordTrace_append hprefix tailTrace_5512238
  have hstable : (prefixWord ++ tailWord_5512238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512238).length < 2 ^ (prefixWord ++ tailWord_5512238).sum := by decide
  have hdescent : baseEnd_5512238 < baseStart_5512238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512262 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_5512262 : Nat := 118140960795 + 5512262 * 2 ^ 59
def prefixEnd_5512262 : Nat := 4983230072969 + 3 ^ 40 * 5512262 * 2
def baseEnd_5512262 : Nat := 2830439899514017483274575

theorem tailTrace_5512262 : CollatzResearch.WordTrace tailWord_5512262 prefixEnd_5512262 2830439899514017483274575 := by
  unfold tailWord_5512262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6282772248625739632640095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134032474637349112162988693 6282772248625739632640095)
  ·
    refine ⟨9424158372938609448960143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6282772248625739632640095 9424158372938609448960143)
    ·
      refine ⟨14136237559407914173440215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9424158372938609448960143 14136237559407914173440215)
      ·
        refine ⟨21204356339111871260160323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14136237559407914173440215 21204356339111871260160323)
        ·
          refine ⟨31806534508667806890240485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21204356339111871260160323 31806534508667806890240485)
          ·
            refine ⟨5963725220375213791920091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31806534508667806890240485 5963725220375213791920091)
            ·
              refine ⟨8945587830562820687880137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5963725220375213791920091 8945587830562820687880137)
              ·
                refine ⟨6709190872922115515910103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8945587830562820687880137 6709190872922115515910103)
                ·
                  refine ⟨10063786309383173273865155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6709190872922115515910103 10063786309383173273865155)
                  ·
                    refine ⟨15095679464074759910797733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10063786309383173273865155 15095679464074759910797733)
                    ·
                      refine ⟨2830439899514017483274575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15095679464074759910797733 2830439899514017483274575)
                      ·
                        rfl

theorem cell23_5512262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_5512262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512262 prefixEnd_5512262 := by exact prefixLift 5512262
  have htrace : WordTrace (prefixWord ++ tailWord_5512262) baseStart_5512262 baseEnd_5512262 := by
    simpa [prefixWord, tailWord_5512262, baseEnd_5512262] using wordTrace_append hprefix tailTrace_5512262
  have hstable : (prefixWord ++ tailWord_5512262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512262).length < 2 ^ (prefixWord ++ tailWord_5512262).sum := by decide
  have hdescent : baseEnd_5512262 < baseStart_5512262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512295 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_5512295 : Nat := 118140960795 + 5512295 * 2 ^ 59
def prefixEnd_5512295 : Nat := 4983230072969 + 3 ^ 40 * 5512295 * 2
def baseEnd_5512295 : Nat := 2830456844375615854161923

theorem tailTrace_5512295 : CollatzResearch.WordTrace tailWord_5512295 prefixEnd_5512295 2830456844375615854161923 := by
  unfold tailWord_5512295
  simp only [CollatzResearch.WordTrace]
  refine ⟨201049915564904114880434339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134033277043269409920289559 201049915564904114880434339)
  ·
    refine ⟨301574873347356172320651509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201049915564904114880434339 301574873347356172320651509)
    ·
      refine ⟨28272644376314641155061079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301574873347356172320651509 28272644376314641155061079)
      ·
        refine ⟨42408966564471961732591619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28272644376314641155061079 42408966564471961732591619)
        ·
          refine ⟨63613449846707942598887429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42408966564471961732591619 63613449846707942598887429)
          ·
            refine ⟨11927521846257739237291393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63613449846707942598887429 11927521846257739237291393)
            ·
              refine ⟨8945641384693304427968545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11927521846257739237291393 8945641384693304427968545)
              ·
                refine ⟨6709231038519978320976409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8945641384693304427968545 6709231038519978320976409)
                ·
                  refine ⟨5031923278889983740732307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6709231038519978320976409 5031923278889983740732307)
                  ·
                    refine ⟨7547884918334975611098461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5031923278889983740732307 7547884918334975611098461)
                    ·
                      refine ⟨2830456844375615854161923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7547884918334975611098461 2830456844375615854161923)
                      ·
                        rfl

theorem cell23_5512295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_5512295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512295 prefixEnd_5512295 := by exact prefixLift 5512295
  have htrace : WordTrace (prefixWord ++ tailWord_5512295) baseStart_5512295 baseEnd_5512295 := by
    simpa [prefixWord, tailWord_5512295, baseEnd_5512295] using wordTrace_append hprefix tailTrace_5512295
  have hstable : (prefixWord ++ tailWord_5512295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512295).length < 2 ^ (prefixWord ++ tailWord_5512295).sum := by decide
  have hdescent : baseEnd_5512295 < baseStart_5512295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512301 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5512301 : Nat := 118140960795 + 5512301 * 2 ^ 59
def prefixEnd_5512301 : Nat := 4983230072969 + 3 ^ 40 * 5512301 * 2
def baseEnd_5512301 : Nat := 2830459925259542830686895

theorem tailTrace_5512301 : CollatzResearch.WordTrace tailWord_5512301 prefixEnd_5512301 2830459925259542830686895 := by
  unfold tailWord_5512301
  simp only [CollatzResearch.WordTrace]
  refine ⟨201050134402882377905152757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134033422935254918603435171 201050134402882377905152757)
  ·
    refine ⟨18848450100270222928608071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201050134402882377905152757 18848450100270222928608071)
    ·
      refine ⟨28272675150405334392912107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18848450100270222928608071 28272675150405334392912107)
      ·
        refine ⟨42409012725608001589368161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28272675150405334392912107 42409012725608001589368161)
        ·
          refine ⟨31806759544206001192026121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42409012725608001589368161 31806759544206001192026121)
          ·
            refine ⟨23855069658154500894019591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31806759544206001192026121 23855069658154500894019591)
            ·
              refine ⟨35782604487231751341029387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23855069658154500894019591 35782604487231751341029387)
              ·
                refine ⟨53673906730847627011544081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35782604487231751341029387 53673906730847627011544081)
                ·
                  refine ⟨40255430048135720258658061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53673906730847627011544081 40255430048135720258658061)
                  ·
                    refine ⟨15095786268050895096996773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40255430048135720258658061 15095786268050895096996773)
                    ·
                      refine ⟨2830459925259542830686895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15095786268050895096996773 2830459925259542830686895)
                      ·
                        rfl

theorem cell23_5512301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5512301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512301 prefixEnd_5512301 := by exact prefixLift 5512301
  have htrace : WordTrace (prefixWord ++ tailWord_5512301) baseStart_5512301 baseEnd_5512301 := by
    simpa [prefixWord, tailWord_5512301, baseEnd_5512301] using wordTrace_append hprefix tailTrace_5512301
  have hstable : (prefixWord ++ tailWord_5512301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512301).length < 2 ^ (prefixWord ++ tailWord_5512301).sum := by decide
  have hdescent : baseEnd_5512301 < baseStart_5512301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512369 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 2, 2, 2]
def baseStart_5512369 : Nat := 118140960795 + 5512369 * 2 ^ 59
def prefixEnd_5512369 : Nat := 4983230072969 + 3 ^ 40 * 5512369 * 2
def baseEnd_5512369 : Nat := 2830494841944048564636583

theorem tailTrace_5512369 : CollatzResearch.WordTrace tailWord_5512369 prefixEnd_5512369 2830494841944048564636583 := by
  unfold tailWord_5512369
  simp only [CollatzResearch.WordTrace]
  refine ⟨201052614566636025518628161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134035076377757350345752107 201052614566636025518628161)
  ·
    refine ⟨150789460924977019138971121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201052614566636025518628161 150789460924977019138971121)
    ·
      refine ⟨113092095693732764354228341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150789460924977019138971121 113092095693732764354228341)
      ·
        refine ⟨10602383971287446658208907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113092095693732764354228341 10602383971287446658208907)
        ·
          refine ⟨15903575956931169987313361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10602383971287446658208907 15903575956931169987313361)
          ·
            refine ⟨11927681967698377490485021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15903575956931169987313361 11927681967698377490485021)
            ·
              refine ⟨4472880737886891558931883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11927681967698377490485021 4472880737886891558931883)
              ·
                refine ⟨6709321106830337338397825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472880737886891558931883 6709321106830337338397825)
                ·
                  refine ⟨5031990830122753003798369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6709321106830337338397825 5031990830122753003798369)
                  ·
                    refine ⟨3773993122592064752848777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5031990830122753003798369 3773993122592064752848777)
                    ·
                      refine ⟨2830494841944048564636583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3773993122592064752848777 2830494841944048564636583)
                      ·
                        rfl

theorem cell23_5512369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_5512369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512369 prefixEnd_5512369 := by exact prefixLift 5512369
  have htrace : WordTrace (prefixWord ++ tailWord_5512369) baseStart_5512369 baseEnd_5512369 := by
    simpa [prefixWord, tailWord_5512369, baseEnd_5512369] using wordTrace_append hprefix tailTrace_5512369
  have hstable : (prefixWord ++ tailWord_5512369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512369).length < 2 ^ (prefixWord ++ tailWord_5512369).sum := by decide
  have hdescent : baseEnd_5512369 < baseStart_5512369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512391 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_5512391 : Nat := 118140960795 + 5512391 * 2 ^ 59
def prefixEnd_5512391 : Nat := 4983230072969 + 3 ^ 40 * 5512391 * 2
def baseEnd_5512391 : Nat := 2830506138518447478561481

theorem tailTrace_5512391 : CollatzResearch.WordTrace tailWord_5512391 prefixEnd_5512391 2830506138518447478561481 := by
  unfold tailWord_5512391
  simp only [CollatzResearch.WordTrace]
  refine ⟨201053416972556323275929027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134035611315037548850619351 201053416972556323275929027)
  ·
    refine ⟨301580125458834484913893541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201053416972556323275929027 301580125458834484913893541)
    ·
      refine ⟨56546273523531465921355039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301580125458834484913893541 56546273523531465921355039)
      ·
        refine ⟨84819410285297198882032559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56546273523531465921355039 84819410285297198882032559)
        ·
          refine ⟨127229115427945798323048839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84819410285297198882032559 127229115427945798323048839)
          ·
            refine ⟨190843673141918697484573259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127229115427945798323048839 190843673141918697484573259)
            ·
              refine ⟨286265509712878046226859889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190843673141918697484573259 286265509712878046226859889)
              ·
                refine ⟨214699132284658534670144917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286265509712878046226859889 214699132284658534670144917)
                ·
                  refine ⟨10064021825843368812663043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214699132284658534670144917 10064021825843368812663043)
                  ·
                    refine ⟨15096032738765053218994565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10064021825843368812663043 15096032738765053218994565)
                    ·
                      refine ⟨2830506138518447478561481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15096032738765053218994565 2830506138518447478561481)
                      ·
                        rfl

theorem cell23_5512391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_5512391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512391 prefixEnd_5512391 := by exact prefixLift 5512391
  have htrace : WordTrace (prefixWord ++ tailWord_5512391) baseStart_5512391 baseEnd_5512391 := by
    simpa [prefixWord, tailWord_5512391, baseEnd_5512391] using wordTrace_append hprefix tailTrace_5512391
  have hstable : (prefixWord ++ tailWord_5512391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512391).length < 2 ^ (prefixWord ++ tailWord_5512391).sum := by decide
  have hdescent : baseEnd_5512391 < baseStart_5512391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512508 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_5512508 : Nat := 118140960795 + 5512508 * 2 ^ 59
def prefixEnd_5512508 : Nat := 4983230072969 + 3 ^ 40 * 5512508 * 2
def baseEnd_5512508 : Nat := 943522071918341173599481

theorem tailTrace_5512508 : CollatzResearch.WordTrace tailWord_5512508 prefixEnd_5512508 943522071918341173599481 := by
  unfold tailWord_5512508
  simp only [CollatzResearch.WordTrace]
  refine ⟨100528842156566226128969089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134038456208754968171958785 100528842156566226128969089)
  ·
    refine ⟨75396631617424669596726817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100528842156566226128969089 75396631617424669596726817)
    ·
      refine ⟨56547473713068502197545113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75396631617424669596726817 56547473713068502197545113)
      ·
        refine ⟨42410605284801376648158835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56547473713068502197545113 42410605284801376648158835)
        ·
          refine ⟨63615907927202064972238253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42410605284801376648158835 63615907927202064972238253)
          ·
            refine ⟨23855965472700774364589345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63615907927202064972238253 23855965472700774364589345)
            ·
              refine ⟨17891974104525580773442009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23855965472700774364589345 17891974104525580773442009)
              ·
                refine ⟨13418980578394185580081507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17891974104525580773442009 13418980578394185580081507)
                ·
                  refine ⟨20128470867591278370122261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13418980578394185580081507 20128470867591278370122261)
                  ·
                    refine ⟨943522071918341173599481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20128470867591278370122261 943522071918341173599481)
                    ·
                      rfl

theorem cell23_5512508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_5512508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512508 prefixEnd_5512508 := by exact prefixLift 5512508
  have htrace : WordTrace (prefixWord ++ tailWord_5512508) baseStart_5512508 baseEnd_5512508 := by
    simpa [prefixWord, tailWord_5512508, baseEnd_5512508] using wordTrace_append hprefix tailTrace_5512508
  have hstable : (prefixWord ++ tailWord_5512508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512508).length < 2 ^ (prefixWord ++ tailWord_5512508).sum := by decide
  have hdescent : baseEnd_5512508 < baseStart_5512508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512515 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 7, 2, 2]
def baseStart_5512515 : Nat := 118140960795 + 5512515 * 2 ^ 59
def prefixEnd_5512515 : Nat := 4983230072969 + 3 ^ 40 * 5512515 * 2
def baseEnd_5512515 : Nat := 2830569810119604993410911

theorem tailTrace_5512515 : CollatzResearch.WordTrace tailWord_5512515 prefixEnd_5512515 2830569810119604993410911 := by
  unfold tailWord_5512515
  simp only [CollatzResearch.WordTrace]
  refine ⟨201057939624107092453442999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134038626416071394968961999 201057939624107092453442999)
  ·
    refine ⟨301586909436160638680164499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201057939624107092453442999 301586909436160638680164499)
    ·
      refine ⟨452380364154240958020246749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301586909436160638680164499 452380364154240958020246749)
      ·
        refine ⟨169642636557840359257592531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 452380364154240958020246749 169642636557840359257592531)
        ·
          refine ⟨254463954836760538886388797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169642636557840359257592531 254463954836760538886388797)
          ·
            refine ⟨95423983063785202082395799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254463954836760538886388797 95423983063785202082395799)
            ·
              refine ⟨143135974595677803123593699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95423983063785202082395799 143135974595677803123593699)
              ·
                refine ⟨214703961893516704685390549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143135974595677803123593699 214703961893516704685390549)
                ·
                  refine ⟨5032124106879297766063841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 214703961893516704685390549 5032124106879297766063841)
                  ·
                    refine ⟨3774093080159473324547881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5032124106879297766063841 3774093080159473324547881)
                    ·
                      refine ⟨2830569810119604993410911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774093080159473324547881 2830569810119604993410911)
                      ·
                        rfl

theorem cell23_5512515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_5512515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512515 prefixEnd_5512515 := by exact prefixLift 5512515
  have htrace : WordTrace (prefixWord ++ tailWord_5512515) baseStart_5512515 baseEnd_5512515 := by
    simpa [prefixWord, tailWord_5512515, baseEnd_5512515] using wordTrace_append hprefix tailTrace_5512515
  have hstable : (prefixWord ++ tailWord_5512515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512515).length < 2 ^ (prefixWord ++ tailWord_5512515).sum := by decide
  have hdescent : baseEnd_5512515 < baseStart_5512515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512588 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_5512588 : Nat := 118140960795 + 5512588 * 2 ^ 59
def prefixEnd_5512588 : Nat := 4983230072969 + 3 ^ 40 * 5512588 * 2
def baseEnd_5512588 : Nat := 2830607294207383207798075

theorem tailTrace_5512588 : CollatzResearch.WordTrace tailWord_5512588 prefixEnd_5512588 2830607294207383207798075 := by
  unfold tailWord_5512588
  simp only [CollatzResearch.WordTrace]
  refine ⟨100530301076421312960425209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134040401435228417280566945 100530301076421312960425209)
  ·
    refine ⟨75397725807315984720318907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100530301076421312960425209 75397725807315984720318907)
    ·
      refine ⟨113096588710973977080478361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75397725807315984720318907 113096588710973977080478361)
      ·
        refine ⟨84822441533230482810358771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113096588710973977080478361 84822441533230482810358771)
        ·
          refine ⟨127233662299845724215538157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84822441533230482810358771 127233662299845724215538157)
          ·
            refine ⟨47712623362442146580826809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127233662299845724215538157 47712623362442146580826809)
            ·
              refine ⟨35784467521831609935620107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47712623362442146580826809 35784467521831609935620107)
              ·
                refine ⟨53676701282747414903430161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35784467521831609935620107 53676701282747414903430161)
                ·
                  refine ⟨40257525962060561177572621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53676701282747414903430161 40257525962060561177572621)
                  ·
                    refine ⟨15096572235772710441589733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40257525962060561177572621 15096572235772710441589733)
                    ·
                      refine ⟨2830607294207383207798075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15096572235772710441589733 2830607294207383207798075)
                      ·
                        rfl

theorem cell23_5512588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_5512588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512588 prefixEnd_5512588 := by exact prefixLift 5512588
  have htrace : WordTrace (prefixWord ++ tailWord_5512588) baseStart_5512588 baseEnd_5512588 := by
    simpa [prefixWord, tailWord_5512588, baseEnd_5512588] using wordTrace_append hprefix tailTrace_5512588
  have hstable : (prefixWord ++ tailWord_5512588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512588).length < 2 ^ (prefixWord ++ tailWord_5512588).sum := by decide
  have hdescent : baseEnd_5512588 < baseStart_5512588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512608 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_5512608 : Nat := 118140960795 + 5512608 * 2 ^ 59
def prefixEnd_5512608 : Nat := 4983230072969 + 3 ^ 40 * 5512608 * 2
def baseEnd_5512608 : Nat := 2830617563820473129547983

theorem tailTrace_5512608 : CollatzResearch.WordTrace tailWord_5512608 prefixEnd_5512608 2830617563820473129547983 := by
  unfold tailWord_5512608
  simp only [CollatzResearch.WordTrace]
  refine ⟨100530665806385084668289239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134040887741846779557718985 100530665806385084668289239)
  ·
    refine ⟨150795998709577627002433859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100530665806385084668289239 150795998709577627002433859)
    ·
      refine ⟨226193998064366440503650789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150795998709577627002433859 226193998064366440503650789)
      ·
        refine ⟨42411374637068707594434523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226193998064366440503650789 42411374637068707594434523)
        ·
          refine ⟨63617061955603061391651785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42411374637068707594434523 63617061955603061391651785)
          ·
            refine ⟨47712796466702296043738839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63617061955603061391651785 47712796466702296043738839)
            ·
              refine ⟨71569194700053444065608259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47712796466702296043738839 71569194700053444065608259)
              ·
                refine ⟨107353792050080166098412389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71569194700053444065608259 107353792050080166098412389)
                ·
                  refine ⟨20128836009390031143452323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107353792050080166098412389 20128836009390031143452323)
                  ·
                    refine ⟨30193254014085046715178485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20128836009390031143452323 30193254014085046715178485)
                    ·
                      refine ⟨2830617563820473129547983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30193254014085046715178485 2830617563820473129547983)
                      ·
                        rfl

theorem cell23_5512608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_5512608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512608 prefixEnd_5512608 := by exact prefixLift 5512608
  have htrace : WordTrace (prefixWord ++ tailWord_5512608) baseStart_5512608 baseEnd_5512608 := by
    simpa [prefixWord, tailWord_5512608, baseEnd_5512608] using wordTrace_append hprefix tailTrace_5512608
  have hstable : (prefixWord ++ tailWord_5512608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512608).length < 2 ^ (prefixWord ++ tailWord_5512608).sum := by decide
  have hdescent : baseEnd_5512608 < baseStart_5512608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512662 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_5512662 : Nat := 118140960795 + 5512662 * 2 ^ 59
def prefixEnd_5512662 : Nat := 4983230072969 + 3 ^ 40 * 5512662 * 2
def baseEnd_5512662 : Nat := 314516143530646213141415

theorem tailTrace_5512662 : CollatzResearch.WordTrace tailWord_5512662 prefixEnd_5512662 314516143530646213141415 := by
  unfold tailWord_5512662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12566456322160908534940265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134042200769716357706029493 12566456322160908534940265)
  ·
    refine ⟨9424842241620681401205199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12566456322160908534940265 9424842241620681401205199)
    ·
      refine ⟨14137263362431022101807799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9424842241620681401205199 14137263362431022101807799)
      ·
        refine ⟨21205895043646533152711699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14137263362431022101807799 21205895043646533152711699)
        ·
          refine ⟨31808842565469799729067549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21205895043646533152711699 31808842565469799729067549)
          ·
            refine ⟨11928315962051174898400331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31808842565469799729067549 11928315962051174898400331)
            ·
              refine ⟨17892473943076762347600497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11928315962051174898400331 17892473943076762347600497)
              ·
                refine ⟨13419355457307571760700373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17892473943076762347600497 13419355457307571760700373)
                ·
                  refine ⟨314516143530646213141415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13419355457307571760700373 314516143530646213141415)
                  ·
                    rfl

theorem cell23_5512662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_5512662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512662 prefixEnd_5512662 := by exact prefixLift 5512662
  have htrace : WordTrace (prefixWord ++ tailWord_5512662) baseStart_5512662 baseEnd_5512662 := by
    simpa [prefixWord, tailWord_5512662, baseEnd_5512662] using wordTrace_append hprefix tailTrace_5512662
  have hstable : (prefixWord ++ tailWord_5512662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512662).length < 2 ^ (prefixWord ++ tailWord_5512662).sum := by decide
  have hdescent : baseEnd_5512662 < baseStart_5512662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512675 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 1, 7]
def baseStart_5512675 : Nat := 118140960795 + 5512675 * 2 ^ 59
def prefixEnd_5512675 : Nat := 4983230072969 + 3 ^ 40 * 5512675 * 2
def baseEnd_5512675 : Nat := 943550655674774789136725

theorem tailTrace_5512675 : CollatzResearch.WordTrace tailWord_5512675 prefixEnd_5512675 943550655674774789136725 := by
  unfold tailWord_5512675
  simp only [CollatzResearch.WordTrace]
  refine ⟨201063775303527439779267479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134042516869018293186178319 201063775303527439779267479)
  ·
    refine ⟨301595662955291159668901219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201063775303527439779267479 301595662955291159668901219)
    ·
      refine ⟨452393494432936739503351829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301595662955291159668901219 452393494432936739503351829)
      ·
        refine ⟨21205945051543909664219617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 452393494432936739503351829 21205945051543909664219617)
        ·
          refine ⟨15904458788657932248164713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21205945051543909664219617 15904458788657932248164713)
          ·
            refine ⟨11928344091493449186123535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15904458788657932248164713 11928344091493449186123535)
            ·
              refine ⟨17892516137240173779185303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11928344091493449186123535 17892516137240173779185303)
              ·
                refine ⟨26838774205860260668777955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17892516137240173779185303 26838774205860260668777955)
                ·
                  refine ⟨40258161308790391003166933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26838774205860260668777955 40258161308790391003166933)
                  ·
                    refine ⟨943550655674774789136725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40258161308790391003166933 943550655674774789136725)
                    ·
                      rfl

theorem cell23_5512675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 7].length) (baseStart_5512675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512675 prefixEnd_5512675 := by exact prefixLift 5512675
  have htrace : WordTrace (prefixWord ++ tailWord_5512675) baseStart_5512675 baseEnd_5512675 := by
    simpa [prefixWord, tailWord_5512675, baseEnd_5512675] using wordTrace_append hprefix tailTrace_5512675
  have hstable : (prefixWord ++ tailWord_5512675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512675).length < 2 ^ (prefixWord ++ tailWord_5512675).sum := by decide
  have hdescent : baseEnd_5512675 < baseStart_5512675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512712 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_5512712 : Nat := 118140960795 + 5512712 * 2 ^ 59
def prefixEnd_5512712 : Nat := 4983230072969 + 3 ^ 40 * 5512712 * 2
def baseEnd_5512712 : Nat := 2830670965808540722647505

theorem tailTrace_5512712 : CollatzResearch.WordTrace tailWord_5512712 prefixEnd_5512712 2830670965808540722647505 := by
  unfold tailWord_5512712
  simp only [CollatzResearch.WordTrace]
  refine ⟨100532562402196697549182195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134043416536262263398909593 100532562402196697549182195)
  ·
    refine ⟨150798843603295046323773293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100532562402196697549182195 150798843603295046323773293)
    ·
      refine ⟨56549566351235642371414985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150798843603295046323773293 56549566351235642371414985)
      ·
        refine ⟨42412174763426731778561239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56549566351235642371414985 42412174763426731778561239)
        ·
          refine ⟨63618262145140097667841859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42412174763426731778561239 63618262145140097667841859)
          ·
            refine ⟨95427393217710146501762789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63618262145140097667841859 95427393217710146501762789)
            ·
              refine ⟨17892636228320652469080523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95427393217710146501762789 17892636228320652469080523)
              ·
                refine ⟨26838954342480978703620785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17892636228320652469080523 26838954342480978703620785)
                ·
                  refine ⟨20129215756860734027715589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26838954342480978703620785 20129215756860734027715589)
                  ·
                    refine ⟨3774227954411387630196673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20129215756860734027715589 3774227954411387630196673)
                    ·
                      refine ⟨2830670965808540722647505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774227954411387630196673 2830670965808540722647505)
                      ·
                        rfl

theorem cell23_5512712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_5512712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512712 prefixEnd_5512712 := by exact prefixLift 5512712
  have htrace : WordTrace (prefixWord ++ tailWord_5512712) baseStart_5512712 baseEnd_5512712 := by
    simpa [prefixWord, tailWord_5512712, baseEnd_5512712] using wordTrace_append hprefix tailTrace_5512712
  have hstable : (prefixWord ++ tailWord_5512712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512712).length < 2 ^ (prefixWord ++ tailWord_5512712).sum := by decide
  have hdescent : baseEnd_5512712 < baseStart_5512712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512732 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_5512732 : Nat := 118140960795 + 5512732 * 2 ^ 59
def prefixEnd_5512732 : Nat := 4983230072969 + 3 ^ 40 * 5512732 * 2
def baseEnd_5512732 : Nat := 2830681235421630644397413

theorem tailTrace_5512732 : CollatzResearch.WordTrace tailWord_5512732 prefixEnd_5512732 2830681235421630644397413 := by
  unfold tailWord_5512732
  simp only [CollatzResearch.WordTrace]
  refine ⟨100532927132160469257046225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134043902842880625676061633 100532927132160469257046225)
  ·
    refine ⟨75399695349120351942784669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100532927132160469257046225 75399695349120351942784669)
    ·
      refine ⟨28274885755920131978544251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75399695349120351942784669 28274885755920131978544251)
      ·
        refine ⟨42412328633880197967816377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28274885755920131978544251 42412328633880197967816377)
        ·
          refine ⟨31809246475410148475862283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42412328633880197967816377 31809246475410148475862283)
          ·
            refine ⟨47713869713115222713793425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31809246475410148475862283 47713869713115222713793425)
            ·
              refine ⟨35785402284836417035345069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47713869713115222713793425 35785402284836417035345069)
              ·
                refine ⟨13419525856813656388254401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35785402284836417035345069 13419525856813656388254401)
                ·
                  refine ⟨10064644392610242291190801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13419525856813656388254401 10064644392610242291190801)
                  ·
                    refine ⟨7548483294457681718393101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10064644392610242291190801 7548483294457681718393101)
                    ·
                      refine ⟨2830681235421630644397413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7548483294457681718393101 2830681235421630644397413)
                      ·
                        rfl

theorem cell23_5512732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_5512732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512732 prefixEnd_5512732 := by exact prefixLift 5512732
  have htrace : WordTrace (prefixWord ++ tailWord_5512732) baseStart_5512732 baseEnd_5512732 := by
    simpa [prefixWord, tailWord_5512732, baseEnd_5512732] using wordTrace_append hprefix tailTrace_5512732
  have hstable : (prefixWord ++ tailWord_5512732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512732).length < 2 ^ (prefixWord ++ tailWord_5512732).sum := by decide
  have hdescent : baseEnd_5512732 < baseStart_5512732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512813 : List Nat := [1, 5, 1, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_5512813 : Nat := 118140960795 + 5512813 * 2 ^ 59
def prefixEnd_5512813 : Nat := 4983230072969 + 3 ^ 40 * 5512813 * 2
def baseEnd_5512813 : Nat := 2830722827354644827484541

theorem tailTrace_5512813 : CollatzResearch.WordTrace tailWord_5512813 prefixEnd_5512813 2830722827354644827484541 := by
  unfold tailWord_5512813
  simp only [CollatzResearch.WordTrace]
  refine ⟨201068808577027489347791093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134045872384684992898527395 201068808577027489347791093)
  ·
    refine ⟨18850200804096327126355415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201068808577027489347791093 18850200804096327126355415)
    ·
      refine ⟨28275301206144490689533123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18850200804096327126355415 28275301206144490689533123)
      ·
        refine ⟨42412951809216736034299685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28275301206144490689533123 42412951809216736034299685)
        ·
          refine ⟨7952428464228138006431191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42412951809216736034299685 7952428464228138006431191)
          ·
            refine ⟨11928642696342207009646787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7952428464228138006431191 11928642696342207009646787)
            ·
              refine ⟨17892964044513310514470181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11928642696342207009646787 17892964044513310514470181)
              ·
                refine ⟨3354930758346245721463159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17892964044513310514470181 3354930758346245721463159)
                ·
                  refine ⟨5032396137519368582194739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354930758346245721463159 5032396137519368582194739)
                  ·
                    refine ⟨7548594206279052873292109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5032396137519368582194739 7548594206279052873292109)
                    ·
                      refine ⟨2830722827354644827484541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7548594206279052873292109 2830722827354644827484541)
                      ·
                        rfl

theorem cell23_5512813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_5512813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512813 prefixEnd_5512813 := by exact prefixLift 5512813
  have htrace : WordTrace (prefixWord ++ tailWord_5512813) baseStart_5512813 baseEnd_5512813 := by
    simpa [prefixWord, tailWord_5512813, baseEnd_5512813] using wordTrace_append hprefix tailTrace_5512813
  have hstable : (prefixWord ++ tailWord_5512813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512813).length < 2 ^ (prefixWord ++ tailWord_5512813).sum := by decide
  have hdescent : baseEnd_5512813 < baseStart_5512813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512815 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_5512815 : Nat := 118140960795 + 5512815 * 2 ^ 59
def prefixEnd_5512815 : Nat := 4983230072969 + 3 ^ 40 * 5512815 * 2
def baseEnd_5512815 : Nat := 2830723854315953819659531

theorem tailTrace_5512815 : CollatzResearch.WordTrace tailWord_5512815 prefixEnd_5512815 2830723854315953819659531 := by
  unfold tailWord_5512815
  simp only [CollatzResearch.WordTrace]
  refine ⟨201068881523020243689363899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134045921015346829126242599 201068881523020243689363899)
  ·
    refine ⟨301603322284530365534045849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201068881523020243689363899 301603322284530365534045849)
    ·
      refine ⟨226202491713397774150534387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301603322284530365534045849 226202491713397774150534387)
      ·
        refine ⟨339303737570096661225801581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226202491713397774150534387 339303737570096661225801581)
        ·
          refine ⟨127238901588786247959675593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339303737570096661225801581 127238901588786247959675593)
          ·
            refine ⟨95429176191589685969756695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127238901588786247959675593 95429176191589685969756695)
            ·
              refine ⟨143143764287384528954635043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95429176191589685969756695 143143764287384528954635043)
              ·
                refine ⟨214715646431076793431952565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143143764287384528954635043 214715646431076793431952565)
                ·
                  refine ⟨20129591852913449384245553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214715646431076793431952565 20129591852913449384245553)
                  ·
                    refine ⟨15097193889685087038184165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20129591852913449384245553 15097193889685087038184165)
                    ·
                      refine ⟨2830723854315953819659531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15097193889685087038184165 2830723854315953819659531)
                      ·
                        rfl

theorem cell23_5512815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_5512815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512815 prefixEnd_5512815 := by exact prefixLift 5512815
  have htrace : WordTrace (prefixWord ++ tailWord_5512815) baseStart_5512815 baseEnd_5512815 := by
    simpa [prefixWord, tailWord_5512815, baseEnd_5512815] using wordTrace_append hprefix tailTrace_5512815
  have hstable : (prefixWord ++ tailWord_5512815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512815).length < 2 ^ (prefixWord ++ tailWord_5512815).sum := by decide
  have hdescent : baseEnd_5512815 < baseStart_5512815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512829 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_5512829 : Nat := 118140960795 + 5512829 * 2 ^ 59
def prefixEnd_5512829 : Nat := 4983230072969 + 3 ^ 40 * 5512829 * 2
def baseEnd_5512829 : Nat := 943577014348372254961489

theorem tailTrace_5512829 : CollatzResearch.WordTrace tailWord_5512829 prefixEnd_5512829 943577014348372254961489 := by
  unfold tailWord_5512829
  simp only [CollatzResearch.WordTrace]
  refine ⟨201069392144969524080373541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134046261429979682720249027 201069392144969524080373541)
  ·
    refine ⟨37700511027181785765070039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201069392144969524080373541 37700511027181785765070039)
    ·
      refine ⟨56550766540772678647605059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37700511027181785765070039 56550766540772678647605059)
      ·
        refine ⟨84826149811159017971407589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56550766540772678647605059 84826149811159017971407589)
        ·
          refine ⟨15904903089592315869638923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84826149811159017971407589 15904903089592315869638923)
          ·
            refine ⟨23857354634388473804458385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15904903089592315869638923 23857354634388473804458385)
            ·
              refine ⟨17893015975791355353343789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23857354634388473804458385 17893015975791355353343789)
              ·
                refine ⟨6709880990921758257503921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17893015975791355353343789 6709880990921758257503921)
                ·
                  refine ⟨5032410743191318693127941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6709880990921758257503921 5032410743191318693127941)
                  ·
                    refine ⟨943577014348372254961489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5032410743191318693127941 943577014348372254961489)
                    ·
                      rfl

theorem cell23_5512829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_5512829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512829 prefixEnd_5512829 := by exact prefixLift 5512829
  have htrace : WordTrace (prefixWord ++ tailWord_5512829) baseStart_5512829 baseEnd_5512829 := by
    simpa [prefixWord, tailWord_5512829, baseEnd_5512829] using wordTrace_append hprefix tailTrace_5512829
  have hstable : (prefixWord ++ tailWord_5512829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512829).length < 2 ^ (prefixWord ++ tailWord_5512829).sum := by decide
  have hdescent : baseEnd_5512829 < baseStart_5512829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512832 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 4]
def baseStart_5512832 : Nat := 118140960795 + 5512832 * 2 ^ 59
def prefixEnd_5512832 : Nat := 4983230072969 + 3 ^ 40 * 5512832 * 2
def baseEnd_5512832 : Nat := 2830732583487080253146953

theorem tailTrace_5512832 : CollatzResearch.WordTrace tailWord_5512832 prefixEnd_5512832 2830732583487080253146953 := by
  unfold tailWord_5512832
  simp only [CollatzResearch.WordTrace]
  refine ⟨100534750781979327796366375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134046334375972437061821833 100534750781979327796366375)
  ·
    refine ⟨150802126172968991694549563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100534750781979327796366375 150802126172968991694549563)
    ·
      refine ⟨226203189259453487541824345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150802126172968991694549563 226203189259453487541824345)
      ·
        refine ⟨169652391944590115656368259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226203189259453487541824345 169652391944590115656368259)
        ·
          refine ⟨254478587916885173484552389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169652391944590115656368259 254478587916885173484552389)
          ·
            refine ⟨47714735234415970028353573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254478587916885173484552389 47714735234415970028353573)
            ·
              refine ⟨8946512856452994380316295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47714735234415970028353573 8946512856452994380316295)
              ·
                refine ⟨13419769284679491570474443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8946512856452994380316295 13419769284679491570474443)
                ·
                  refine ⟨20129653927019237355711665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13419769284679491570474443 20129653927019237355711665)
                  ·
                    refine ⟨15097240445264428016783749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20129653927019237355711665 15097240445264428016783749)
                    ·
                      refine ⟨2830732583487080253146953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15097240445264428016783749 2830732583487080253146953)
                      ·
                        rfl

theorem cell23_5512832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_5512832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512832 prefixEnd_5512832 := by exact prefixLift 5512832
  have htrace : WordTrace (prefixWord ++ tailWord_5512832) baseStart_5512832 baseEnd_5512832 := by
    simpa [prefixWord, tailWord_5512832, baseEnd_5512832] using wordTrace_append hprefix tailTrace_5512832
  have hstable : (prefixWord ++ tailWord_5512832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512832).length < 2 ^ (prefixWord ++ tailWord_5512832).sum := by decide
  have hdescent : baseEnd_5512832 < baseStart_5512832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512840 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5512840 : Nat := 118140960795 + 5512840 * 2 ^ 59
def prefixEnd_5512840 : Nat := 4983230072969 + 3 ^ 40 * 5512840 * 2
def baseEnd_5512840 : Nat := 2830736691332316221846917

theorem tailTrace_5512840 : CollatzResearch.WordTrace tailWord_5512840 prefixEnd_5512840 2830736691332316221846917 := by
  unfold tailWord_5512840
  simp only [CollatzResearch.WordTrace]
  refine ⟨100534896673964836479511987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134046528898619781972682649 100534896673964836479511987)
  ·
    refine ⟨150802345010947254719267981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100534896673964836479511987 150802345010947254719267981)
    ·
      refine ⟨56550879379105220519725493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150802345010947254719267981 56550879379105220519725493)
      ·
        refine ⟨5301644941791114423724265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56550879379105220519725493 5301644941791114423724265)
        ·
          refine ⟨3976233706343335817793199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5301644941791114423724265 3976233706343335817793199)
          ·
            refine ⟨5964350559515003726689799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3976233706343335817793199 5964350559515003726689799)
            ·
              refine ⟨8946525839272505590034699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5964350559515003726689799 8946525839272505590034699)
              ·
                refine ⟨13419788758908758385052049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8946525839272505590034699 13419788758908758385052049)
                ·
                  refine ⟨10064841569181568788789037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13419788758908758385052049 10064841569181568788789037)
                  ·
                    refine ⟨3774315588443088295795889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10064841569181568788789037 3774315588443088295795889)
                    ·
                      refine ⟨2830736691332316221846917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774315588443088295795889 2830736691332316221846917)
                      ·
                        rfl

theorem cell23_5512840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5512840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512840 prefixEnd_5512840 := by exact prefixLift 5512840
  have htrace : WordTrace (prefixWord ++ tailWord_5512840) baseStart_5512840 baseEnd_5512840 := by
    simpa [prefixWord, tailWord_5512840, baseEnd_5512840] using wordTrace_append hprefix tailTrace_5512840
  have hstable : (prefixWord ++ tailWord_5512840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512840).length < 2 ^ (prefixWord ++ tailWord_5512840).sum := by decide
  have hdescent : baseEnd_5512840 < baseStart_5512840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512856 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 1, 2, 3]
def baseStart_5512856 : Nat := 118140960795 + 5512856 * 2 ^ 59
def prefixEnd_5512856 : Nat := 4983230072969 + 3 ^ 40 * 5512856 * 2
def baseEnd_5512856 : Nat := 2830744907022788159246843

theorem tailTrace_5512856 : CollatzResearch.WordTrace tailWord_5512856 prefixEnd_5512856 2830744907022788159246843 := by
  unfold tailWord_5512856
  simp only [CollatzResearch.WordTrace]
  refine ⟨100535188457935853845803211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134046917943914471794404281 100535188457935853845803211)
  ·
    refine ⟨150802782686903780768704817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100535188457935853845803211 150802782686903780768704817)
    ·
      refine ⟨113102087015177835576528613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150802782686903780768704817 113102087015177835576528613)
      ·
        refine ⟨21206641315345844170599115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113102087015177835576528613 21206641315345844170599115)
        ·
          refine ⟨31809961973018766255898673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21206641315345844170599115 31809961973018766255898673)
          ·
            refine ⟨23857471479764074691924005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31809961973018766255898673 23857471479764074691924005)
            ·
              refine ⟨4473275902455764004735751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23857471479764074691924005 4473275902455764004735751)
              ·
                refine ⟨6709913853683646007103627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473275902455764004735751 6709913853683646007103627)
                ·
                  refine ⟨10064870780525469010655441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6709913853683646007103627 10064870780525469010655441)
                  ·
                    refine ⟨7548653085394101757991581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10064870780525469010655441 7548653085394101757991581)
                    ·
                      refine ⟨2830744907022788159246843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7548653085394101757991581 2830744907022788159246843)
                      ·
                        rfl

theorem cell23_5512856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_5512856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512856 prefixEnd_5512856 := by exact prefixLift 5512856
  have htrace : WordTrace (prefixWord ++ tailWord_5512856) baseStart_5512856 baseEnd_5512856 := by
    simpa [prefixWord, tailWord_5512856, baseEnd_5512856] using wordTrace_append hprefix tailTrace_5512856
  have hstable : (prefixWord ++ tailWord_5512856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512856).length < 2 ^ (prefixWord ++ tailWord_5512856).sum := by decide
  have hdescent : baseEnd_5512856 < baseStart_5512856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512863 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 2, 4]
def baseStart_5512863 : Nat := 118140960795 + 5512863 * 2 ^ 59
def prefixEnd_5512863 : Nat := 4983230072969 + 3 ^ 40 * 5512863 * 2
def baseEnd_5512863 : Nat := 943582833795789877286437

theorem tailTrace_5512863 : CollatzResearch.WordTrace tailWord_5512863 prefixEnd_5512863 943582833795789877286437 := by
  unfold tailWord_5512863
  simp only [CollatzResearch.WordTrace]
  refine ⟨201070632226846347887111243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134047088151230898591407495 201070632226846347887111243)
  ·
    refine ⟨301605948340269521830666865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201070632226846347887111243 301605948340269521830666865)
    ·
      refine ⟨226204461255202141373000149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301605948340269521830666865 226204461255202141373000149)
      ·
        refine ⟨5301667060668800188429691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 226204461255202141373000149 5301667060668800188429691)
        ·
          refine ⟨7952500591003200282644537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5301667060668800188429691 7952500591003200282644537)
          ·
            refine ⟨5964375443252400211983403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7952500591003200282644537 5964375443252400211983403)
            ·
              refine ⟨8946563164878600317975105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5964375443252400211983403 8946563164878600317975105)
              ·
                refine ⟨6709922373658950238481329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8946563164878600317975105 6709922373658950238481329)
                ·
                  refine ⟨5032441780244212678860997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6709922373658950238481329 5032441780244212678860997)
                  ·
                    refine ⟨943582833795789877286437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5032441780244212678860997 943582833795789877286437)
                    ·
                      rfl

theorem cell23_5512863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 4].length) (baseStart_5512863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512863 prefixEnd_5512863 := by exact prefixLift 5512863
  have htrace : WordTrace (prefixWord ++ tailWord_5512863) baseStart_5512863 baseEnd_5512863 := by
    simpa [prefixWord, tailWord_5512863, baseEnd_5512863] using wordTrace_append hprefix tailTrace_5512863
  have hstable : (prefixWord ++ tailWord_5512863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512863).length < 2 ^ (prefixWord ++ tailWord_5512863).sum := by decide
  have hdescent : baseEnd_5512863 < baseStart_5512863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512896 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 1, 3, 2]
def baseStart_5512896 : Nat := 118140960795 + 5512896 * 2 ^ 59
def prefixEnd_5512896 : Nat := 4983230072969 + 3 ^ 40 * 5512896 * 2
def baseEnd_5512896 : Nat := 2830765446248968002746659

theorem tailTrace_5512896 : CollatzResearch.WordTrace tailWord_5512896 prefixEnd_5512896 2830765446248968002746659 := by
  unfold tailWord_5512896
  simp only [CollatzResearch.WordTrace]
  refine ⟨100535917917863397261531271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134047890557151196348708361 100535917917863397261531271)
  ·
    refine ⟨150803876876795095892296907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100535917917863397261531271 150803876876795095892296907)
    ·
      refine ⟨226205815315192643838445361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150803876876795095892296907 226205815315192643838445361)
      ·
        refine ⟨169654361486394482878834021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226205815315192643838445361 169654361486394482878834021)
        ·
          refine ⟨31810192778698965539781379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169654361486394482878834021 31810192778698965539781379)
          ·
            refine ⟨47715289168048448309672069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31810192778698965539781379 47715289168048448309672069)
            ·
              refine ⟨8946616719009084058063513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47715289168048448309672069 8946616719009084058063513)
              ·
                refine ⟨6709962539256813043547635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8946616719009084058063513 6709962539256813043547635)
                ·
                  refine ⟨10064943808885219565321453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6709962539256813043547635 10064943808885219565321453)
                  ·
                    refine ⟨3774353928331957336995545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10064943808885219565321453 3774353928331957336995545)
                    ·
                      refine ⟨2830765446248968002746659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774353928331957336995545 2830765446248968002746659)
                      ·
                        rfl

theorem cell23_5512896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_5512896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512896 prefixEnd_5512896 := by exact prefixLift 5512896
  have htrace : WordTrace (prefixWord ++ tailWord_5512896) baseStart_5512896 baseEnd_5512896 := by
    simpa [prefixWord, tailWord_5512896, baseEnd_5512896] using wordTrace_append hprefix tailTrace_5512896
  have hstable : (prefixWord ++ tailWord_5512896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512896).length < 2 ^ (prefixWord ++ tailWord_5512896).sum := by decide
  have hdescent : baseEnd_5512896 < baseStart_5512896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512972 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_5512972 : Nat := 118140960795 + 5512972 * 2 ^ 59
def prefixEnd_5512972 : Nat := 4983230072969 + 3 ^ 40 * 5512972 * 2
def baseEnd_5512972 : Nat := 2830804470778709705396309

theorem tailTrace_5512972 : CollatzResearch.WordTrace tailWord_5512972 prefixEnd_5512972 2830804470778709705396309 := by
  unfold tailWord_5512972
  simp only [CollatzResearch.WordTrace]
  refine ⟨100537303891725729751414585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134049738522300973001886113 100537303891725729751414585)
  ·
    refine ⟨75402977918794297313560939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100537303891725729751414585 75402977918794297313560939)
    ·
      refine ⟨113104466878191445970341409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75402977918794297313560939 113104466878191445970341409)
      ·
        refine ⟨84828350158643584477756057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113104466878191445970341409 84828350158643584477756057)
        ·
          refine ⟨63621262618982688358317043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84828350158643584477756057 63621262618982688358317043)
          ·
            refine ⟨95431893928474032537475565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63621262618982688358317043 95431893928474032537475565)
            ·
              refine ⟨35786960223177762201553337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95431893928474032537475565 35786960223177762201553337)
              ·
                refine ⟨26840220167383321651165003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35786960223177762201553337 26840220167383321651165003)
                ·
                  refine ⟨40260330251074982476747505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26840220167383321651165003 40260330251074982476747505)
                  ·
                    refine ⟨30195247688306236857560629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40260330251074982476747505 30195247688306236857560629)
                    ·
                      refine ⟨2830804470778709705396309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30195247688306236857560629 2830804470778709705396309)
                      ·
                        rfl

theorem cell23_5512972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_5512972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512972 prefixEnd_5512972 := by exact prefixLift 5512972
  have htrace : WordTrace (prefixWord ++ tailWord_5512972) baseStart_5512972 baseEnd_5512972 := by
    simpa [prefixWord, tailWord_5512972, baseEnd_5512972] using wordTrace_append hprefix tailTrace_5512972
  have hstable : (prefixWord ++ tailWord_5512972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512972).length < 2 ^ (prefixWord ++ tailWord_5512972).sum := by decide
  have hdescent : baseEnd_5512972 < baseStart_5512972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5512983 : List Nat := [1, 1, 3, 4, 2, 3, 2, 2, 5]
def baseStart_5512983 : Nat := 118140960795 + 5512983 * 2 ^ 59
def prefixEnd_5512983 : Nat := 4983230072969 + 3 ^ 40 * 5512983 * 2
def baseEnd_5512983 : Nat := 314534457673989906928751

theorem tailTrace_5512983 : CollatzResearch.WordTrace tailWord_5512983 prefixEnd_5512983 314534457673989906928751 := by
  unfold tailWord_5512983
  simp only [CollatzResearch.WordTrace]
  refine ⟨201075008986411608381479603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134050005990941072254319735 201075008986411608381479603)
  ·
    refine ⟨301612513479617412572219405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201075008986411608381479603 301612513479617412572219405)
    ·
      refine ⟨113104692554856529714582277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301612513479617412572219405 113104692554856529714582277)
      ·
        refine ⟨21207129854035599321484177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113104692554856529714582277 21207129854035599321484177)
        ·
          refine ⟨15905347390526699491113133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21207129854035599321484177 15905347390526699491113133)
          ·
            refine ⟨5964505271447512309167425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15905347390526699491113133 5964505271447512309167425)
            ·
              refine ⟨4473378953585634231875569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5964505271447512309167425 4473378953585634231875569)
              ·
                refine ⟨3355034215189225673906677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4473378953585634231875569 3355034215189225673906677)
                ·
                  refine ⟨314534457673989906928751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3355034215189225673906677 314534457673989906928751)
                  ·
                    rfl

theorem cell23_5512983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 5].length) (baseStart_5512983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5512983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5512983 prefixEnd_5512983 := by exact prefixLift 5512983
  have htrace : WordTrace (prefixWord ++ tailWord_5512983) baseStart_5512983 baseEnd_5512983 := by
    simpa [prefixWord, tailWord_5512983, baseEnd_5512983] using wordTrace_append hprefix tailTrace_5512983
  have hstable : (prefixWord ++ tailWord_5512983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5512983).length < 2 ^ (prefixWord ++ tailWord_5512983).sum := by decide
  have hdescent : baseEnd_5512983 < baseStart_5512983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5512983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513009 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 5, 4]
def baseStart_5513009 : Nat := 118140960795 + 5513009 * 2 ^ 59
def prefixEnd_5513009 : Nat := 4983230072969 + 3 ^ 40 * 5513009 * 2
def baseEnd_5513009 : Nat := 943607823187642020211213

theorem tailTrace_5513009 : CollatzResearch.WordTrace tailWord_5513009 prefixEnd_5513009 943607823187642020211213 := by
  unfold tailWord_5513009
  simp only [CollatzResearch.WordTrace]
  refine ⟨201075957284317414821926081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134050638189544943214617387 201075957284317414821926081)
  ·
    refine ⟨150806967963238061116444561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201075957284317414821926081 150806967963238061116444561)
    ·
      refine ⟨113105225972428545837333421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150806967963238061116444561 113105225972428545837333421)
      ·
        refine ⟨42414459739660704689000033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113105225972428545837333421 42414459739660704689000033)
        ·
          refine ⟨31810844804745528516750025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42414459739660704689000033 31810844804745528516750025)
          ·
            refine ⟨23858133603559146387562519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31810844804745528516750025 23858133603559146387562519)
            ·
              refine ⟨35787200405338719581343779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23858133603559146387562519 35787200405338719581343779)
              ·
                refine ⟨53680800608008079372015669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35787200405338719581343779 53680800608008079372015669)
                ·
                  refine ⟨5032575057000757441126469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53680800608008079372015669 5032575057000757441126469)
                  ·
                    refine ⟨943607823187642020211213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5032575057000757441126469 943607823187642020211213)
                    ·
                      rfl

theorem cell23_5513009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_5513009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513009 prefixEnd_5513009 := by exact prefixLift 5513009
  have htrace : WordTrace (prefixWord ++ tailWord_5513009) baseStart_5513009 baseEnd_5513009 := by
    simpa [prefixWord, tailWord_5513009, baseEnd_5513009] using wordTrace_append hprefix tailTrace_5513009
  have hstable : (prefixWord ++ tailWord_5513009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513009).length < 2 ^ (prefixWord ++ tailWord_5513009).sum := by decide
  have hdescent : baseEnd_5513009 < baseStart_5513009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513013 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_5513013 : Nat := 118140960795 + 5513013 * 2 ^ 59
def prefixEnd_5513013 : Nat := 4983230072969 + 3 ^ 40 * 5513013 * 2
def baseEnd_5513013 : Nat := 943608507828514681661207

theorem tailTrace_5513013 : CollatzResearch.WordTrace tailWord_5513013 prefixEnd_5513013 943608507828514681661207 := by
  unfold tailWord_5513013
  simp only [CollatzResearch.WordTrace]
  refine ⟨201076103176302923505071693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134050735450868615670047795 201076103176302923505071693)
  ·
    refine ⟨75403538691113596314401885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201076103176302923505071693 75403538691113596314401885)
    ·
      refine ⟨28276327009167598617900707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75403538691113596314401885 28276327009167598617900707)
      ·
        refine ⟨42414490513751397926851061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28276327009167598617900707 42414490513751397926851061)
        ·
          refine ⟨3976358485664193555642287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42414490513751397926851061 3976358485664193555642287)
          ·
            refine ⟨5964537728496290333463431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3976358485664193555642287 5964537728496290333463431)
            ·
              refine ⟨8946806592744435500195147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5964537728496290333463431 8946806592744435500195147)
              ·
                refine ⟨13420209889116653250292721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8946806592744435500195147 13420209889116653250292721)
                ·
                  refine ⟨10065157416837489937719541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13420209889116653250292721 10065157416837489937719541)
                  ·
                    refine ⟨943608507828514681661207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10065157416837489937719541 943608507828514681661207)
                    ·
                      rfl

theorem cell23_5513013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_5513013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513013 prefixEnd_5513013 := by exact prefixLift 5513013
  have htrace : WordTrace (prefixWord ++ tailWord_5513013) baseStart_5513013 baseEnd_5513013 := by
    simpa [prefixWord, tailWord_5513013, baseEnd_5513013] using wordTrace_append hprefix tailTrace_5513013
  have hstable : (prefixWord ++ tailWord_5513013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513013).length < 2 ^ (prefixWord ++ tailWord_5513013).sum := by decide
  have hdescent : baseEnd_5513013 < baseStart_5513013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513016 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_5513016 : Nat := 118140960795 + 5513016 * 2 ^ 59
def prefixEnd_5513016 : Nat := 4983230072969 + 3 ^ 40 * 5513016 * 2
def baseEnd_5513016 : Nat := 2830827063927507533246107

theorem tailTrace_5513016 : CollatzResearch.WordTrace tailWord_5513016 prefixEnd_5513016 2830827063927507533246107 := by
  unfold tailWord_5513016
  simp only [CollatzResearch.WordTrace]
  refine ⟨100538106297646027508715451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134050808396861370011620601 100538106297646027508715451)
  ·
    refine ⟨150807159446469041263073177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100538106297646027508715451 150807159446469041263073177)
    ·
      refine ⟨113105369584851780947304883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150807159446469041263073177 113105369584851780947304883)
      ·
        refine ⟨169658054377277671420957325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113105369584851780947304883 169658054377277671420957325)
        ·
          refine ⟨63621770391479126782858997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169658054377277671420957325 63621770391479126782858997)
          ·
            refine ⟨5964540974201168135893031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63621770391479126782858997 5964540974201168135893031)
            ·
              refine ⟨8946811461301752203839547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5964540974201168135893031 8946811461301752203839547)
              ·
                refine ⟨13420217191952628305759321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8946811461301752203839547 13420217191952628305759321)
                ·
                  refine ⟨10065162893964471229319491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13420217191952628305759321 10065162893964471229319491)
                  ·
                    refine ⟨15097744340946706843979237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10065162893964471229319491 15097744340946706843979237)
                    ·
                      refine ⟨2830827063927507533246107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15097744340946706843979237 2830827063927507533246107)
                      ·
                        rfl

theorem cell23_5513016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_5513016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513016 prefixEnd_5513016 := by exact prefixLift 5513016
  have htrace : WordTrace (prefixWord ++ tailWord_5513016) baseStart_5513016 baseEnd_5513016 := by
    simpa [prefixWord, tailWord_5513016, baseEnd_5513016] using wordTrace_append hprefix tailTrace_5513016
  have hstable : (prefixWord ++ tailWord_5513016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513016).length < 2 ^ (prefixWord ++ tailWord_5513016).sum := by decide
  have hdescent : baseEnd_5513016 < baseStart_5513016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513056 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 6]
def baseStart_5513056 : Nat := 118140960795 + 5513056 * 2 ^ 59
def prefixEnd_5513056 : Nat := 4983230072969 + 3 ^ 40 * 5513056 * 2
def baseEnd_5513056 : Nat := 314538622572631930749547

theorem tailTrace_5513056 : CollatzResearch.WordTrace tailWord_5513056 prefixEnd_5513056 314538622572631930749547 := by
  unfold tailWord_5513056
  simp only [CollatzResearch.WordTrace]
  refine ⟨100538835757573570924443511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134051781010098094565924681 100538835757573570924443511)
  ·
    refine ⟨150808253636360356386665267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100538835757573570924443511 150808253636360356386665267)
    ·
      refine ⟨226212380454540534579997901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150808253636360356386665267 226212380454540534579997901)
      ·
        refine ⟨84829642670452700467499213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226212380454540534579997901 84829642670452700467499213)
        ·
          refine ⟨31811116001419762675312205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84829642670452700467499213 31811116001419762675312205)
          ·
            refine ⟨11929168500532411003242077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31811116001419762675312205 11929168500532411003242077)
            ·
              refine ⟨4473438187699654126215779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11929168500532411003242077 4473438187699654126215779)
              ·
                refine ⟨6710157281549481189323669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473438187699654126215779 6710157281549481189323669)
                ·
                  refine ⟨314538622572631930749547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6710157281549481189323669 314538622572631930749547)
                  ·
                    rfl

theorem cell23_5513056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 6].length) (baseStart_5513056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513056 prefixEnd_5513056 := by exact prefixLift 5513056
  have htrace : WordTrace (prefixWord ++ tailWord_5513056) baseStart_5513056 baseEnd_5513056 := by
    simpa [prefixWord, tailWord_5513056, baseEnd_5513056] using wordTrace_append hprefix tailTrace_5513056
  have hstable : (prefixWord ++ tailWord_5513056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513056).length < 2 ^ (prefixWord ++ tailWord_5513056).sum := by decide
  have hdescent : baseEnd_5513056 < baseStart_5513056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513069 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_5513069 : Nat := 118140960795 + 5513069 * 2 ^ 59
def prefixEnd_5513069 : Nat := 4983230072969 + 3 ^ 40 * 5513069 * 2
def baseEnd_5513069 : Nat := 943618092800731941961121

theorem tailTrace_5513069 : CollatzResearch.WordTrace tailWord_5513069 prefixEnd_5513069 943618092800731941961121 := by
  unfold tailWord_5513069
  simp only [CollatzResearch.WordTrace]
  refine ⟨201078145664100045069110261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134052097109400030046073507 201078145664100045069110261)
  ·
    refine ⟨18851076156009379225229087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201078145664100045069110261 18851076156009379225229087)
    ·
      refine ⟨28276614234014068837843631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18851076156009379225229087 28276614234014068837843631)
      ·
        refine ⟨42414921351021103256765447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28276614234014068837843631 42414921351021103256765447)
        ·
          refine ⟨63622382026531654885148171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42414921351021103256765447 63622382026531654885148171)
          ·
            refine ⟨95433573039797482327722257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63622382026531654885148171 95433573039797482327722257)
            ·
              refine ⟨71575179779848111745791693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95433573039797482327722257 71575179779848111745791693)
              ·
                refine ⟨26840692417443041904671885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71575179779848111745791693 26840692417443041904671885)
                ·
                  refine ⟨10065259656541140714251957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26840692417443041904671885 10065259656541140714251957)
                  ·
                    refine ⟨943618092800731941961121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10065259656541140714251957 943618092800731941961121)
                    ·
                      rfl

theorem cell23_5513069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_5513069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513069 prefixEnd_5513069 := by exact prefixLift 5513069
  have htrace : WordTrace (prefixWord ++ tailWord_5513069) baseStart_5513069 baseEnd_5513069 := by
    simpa [prefixWord, tailWord_5513069, baseEnd_5513069] using wordTrace_append hprefix tailTrace_5513069
  have hstable : (prefixWord ++ tailWord_5513069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513069).length < 2 ^ (prefixWord ++ tailWord_5513069).sum := by decide
  have hdescent : baseEnd_5513069 < baseStart_5513069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513109 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_5513109 : Nat := 118140960795 + 5513109 * 2 ^ 59
def prefixEnd_5513109 : Nat := 4983230072969 + 3 ^ 40 * 5513109 * 2
def baseEnd_5513109 : Nat := 2830874817628375669383179

theorem tailTrace_5513109 : CollatzResearch.WordTrace tailWord_5513109 prefixEnd_5513109 2830874817628375669383179 := by
  unfold tailWord_5513109
  simp only [CollatzResearch.WordTrace]
  refine ⟨201079604583955131900566381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134053069722636754600377587 201079604583955131900566381)
  ·
    refine ⟨75404851718983174462712393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201079604583955131900566381 75404851718983174462712393)
    ·
      refine ⟨56553638789237380847034295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75404851718983174462712393 56553638789237380847034295)
      ·
        refine ⟨84830458183856071270551443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56553638789237380847034295 84830458183856071270551443)
        ·
          refine ⟨127245687275784106905827165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84830458183856071270551443 127245687275784106905827165)
          ·
            refine ⟨47717132728419040089685187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127245687275784106905827165 47717132728419040089685187)
            ·
              refine ⟨71575699092628560134527781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47717132728419040089685187 71575699092628560134527781)
              ·
                refine ⟨13420443579867855025223959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71575699092628560134527781 13420443579867855025223959)
                ·
                  refine ⟨20130665369801782537835939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13420443579867855025223959 20130665369801782537835939)
                  ·
                    refine ⟨30195998054702673806753909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20130665369801782537835939 30195998054702673806753909)
                    ·
                      refine ⟨2830874817628375669383179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30195998054702673806753909 2830874817628375669383179)
                      ·
                        rfl

theorem cell23_5513109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_5513109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513109 prefixEnd_5513109 := by exact prefixLift 5513109
  have htrace : WordTrace (prefixWord ++ tailWord_5513109) baseStart_5513109 baseEnd_5513109 := by
    simpa [prefixWord, tailWord_5513109, baseEnd_5513109] using wordTrace_append hprefix tailTrace_5513109
  have hstable : (prefixWord ++ tailWord_5513109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513109).length < 2 ^ (prefixWord ++ tailWord_5513109).sum := by decide
  have hdescent : baseEnd_5513109 < baseStart_5513109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513173 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_5513173 : Nat := 118140960795 + 5513173 * 2 ^ 59
def prefixEnd_5513173 : Nat := 4983230072969 + 3 ^ 40 * 5513173 * 2
def baseEnd_5513173 : Nat := 2830907680390263418982885

theorem tailTrace_5513173 : CollatzResearch.WordTrace tailWord_5513173 prefixEnd_5513173 2830907680390263418982885 := by
  unfold tailWord_5513173
  simp only [CollatzResearch.WordTrace]
  refine ⟨201081938855723270830896173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134054625903815513887264115 201081938855723270830896173)
  ·
    refine ⟨75405727070896226561586065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201081938855723270830896173 75405727070896226561586065)
    ·
      refine ⟨56554295303172169921189549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75405727070896226561586065 56554295303172169921189549)
      ·
        refine ⟨21207860738689563720446081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56554295303172169921189549 21207860738689563720446081)
        ·
          refine ⟨15905895554017172790334561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21207860738689563720446081 15905895554017172790334561)
          ·
            refine ⟨11929421665512879592750921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15905895554017172790334561 11929421665512879592750921)
            ·
              refine ⟨8947066249134659694563191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11929421665512879592750921 8947066249134659694563191)
              ·
                refine ⟨13420599373701989541844787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8947066249134659694563191 13420599373701989541844787)
                ·
                  refine ⟨20130899060552984312767181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13420599373701989541844787 20130899060552984312767181)
                  ·
                    refine ⟨7549087147707369117287693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20130899060552984312767181 7549087147707369117287693)
                    ·
                      refine ⟨2830907680390263418982885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7549087147707369117287693 2830907680390263418982885)
                      ·
                        rfl

theorem cell23_5513173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_5513173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513173 prefixEnd_5513173 := by exact prefixLift 5513173
  have htrace : WordTrace (prefixWord ++ tailWord_5513173) baseStart_5513173 baseEnd_5513173 := by
    simpa [prefixWord, tailWord_5513173, baseEnd_5513173] using wordTrace_append hprefix tailTrace_5513173
  have hstable : (prefixWord ++ tailWord_5513173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513173).length < 2 ^ (prefixWord ++ tailWord_5513173).sum := by decide
  have hdescent : baseEnd_5513173 < baseStart_5513173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513183 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 3, 3, 2]
def baseStart_5513183 : Nat := 118140960795 + 5513183 * 2 ^ 59
def prefixEnd_5513183 : Nat := 4983230072969 + 3 ^ 40 * 5513183 * 2
def baseEnd_5513183 : Nat := 2830912815196808379857839

theorem tailTrace_5513183 : CollatzResearch.WordTrace tailWord_5513183 prefixEnd_5513183 2830912815196808379857839 := by
  unfold tailWord_5513183
  simp only [CollatzResearch.WordTrace]
  refine ⟨201082303585687042538760203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134054869057124695025840135 201082303585687042538760203)
  ·
    refine ⟨301623455378530563808140305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201082303585687042538760203 301623455378530563808140305)
    ·
      refine ⟨226217591533897922856105229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301623455378530563808140305 226217591533897922856105229)
      ·
        refine ⟨84831596825211721071039461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226217591533897922856105229 84831596825211721071039461)
        ·
          refine ⟨15905924404727197700819899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84831596825211721071039461 15905924404727197700819899)
          ·
            refine ⟨23858886607090796551229849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15905924404727197700819899 23858886607090796551229849)
            ·
              refine ⟨17894164955318097413422387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23858886607090796551229849 17894164955318097413422387)
              ·
                refine ⟨26841247432977146120133581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17894164955318097413422387 26841247432977146120133581)
                ·
                  refine ⟨10065467787366429795050093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26841247432977146120133581 10065467787366429795050093)
                  ·
                    refine ⟨3774550420262411173143785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10065467787366429795050093 3774550420262411173143785)
                    ·
                      refine ⟨2830912815196808379857839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774550420262411173143785 2830912815196808379857839)
                      ·
                        rfl

theorem cell23_5513183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_5513183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513183 prefixEnd_5513183 := by exact prefixLift 5513183
  have htrace : WordTrace (prefixWord ++ tailWord_5513183) baseStart_5513183 baseEnd_5513183 := by
    simpa [prefixWord, tailWord_5513183, baseEnd_5513183] using wordTrace_append hprefix tailTrace_5513183
  have hstable : (prefixWord ++ tailWord_5513183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513183).length < 2 ^ (prefixWord ++ tailWord_5513183).sum := by decide
  have hdescent : baseEnd_5513183 < baseStart_5513183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513199 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_5513199 : Nat := 118140960795 + 5513199 * 2 ^ 59
def prefixEnd_5513199 : Nat := 4983230072969 + 3 ^ 40 * 5513199 * 2
def baseEnd_5513199 : Nat := 2830921030887280317257765

theorem tailTrace_5513199 : CollatzResearch.WordTrace tailWord_5513199 prefixEnd_5513199 2830921030887280317257765 := by
  unfold tailWord_5513199
  simp only [CollatzResearch.WordTrace]
  refine ⟨201082887153629077271342651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134055258102419384847561767 201082887153629077271342651)
  ·
    refine ⟨301624330730443615907013977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201082887153629077271342651 301624330730443615907013977)
    ·
      refine ⟨226218248047832711930260483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301624330730443615907013977 226218248047832711930260483)
      ·
        refine ⟨339327372071749067895390725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226218248047832711930260483 339327372071749067895390725)
        ·
          refine ⟨63623882263452950230385761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339327372071749067895390725 63623882263452950230385761)
          ·
            refine ⟨47717911697589712672789321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63623882263452950230385761 47717911697589712672789321)
            ·
              refine ⟨35788433773192284504591991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47717911697589712672789321 35788433773192284504591991)
              ·
                refine ⟨53682650659788426756887987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35788433773192284504591991 53682650659788426756887987)
                ·
                  refine ⟨80523975989682640135331981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53682650659788426756887987 80523975989682640135331981)
                  ·
                    refine ⟨30196490996130990050749493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80523975989682640135331981 30196490996130990050749493)
                    ·
                      refine ⟨2830921030887280317257765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30196490996130990050749493 2830921030887280317257765)
                      ·
                        rfl

theorem cell23_5513199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_5513199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513199 prefixEnd_5513199 := by exact prefixLift 5513199
  have htrace : WordTrace (prefixWord ++ tailWord_5513199) baseStart_5513199 baseEnd_5513199 := by
    simpa [prefixWord, tailWord_5513199, baseEnd_5513199] using wordTrace_append hprefix tailTrace_5513199
  have hstable : (prefixWord ++ tailWord_5513199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513199).length < 2 ^ (prefixWord ++ tailWord_5513199).sum := by decide
  have hdescent : baseEnd_5513199 < baseStart_5513199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513200 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 1, 3, 2]
def baseStart_5513200 : Nat := 118140960795 + 5513200 * 2 ^ 59
def prefixEnd_5513200 : Nat := 4983230072969 + 3 ^ 40 * 5513200 * 2
def baseEnd_5513200 : Nat := 2830921544367934813345261

theorem tailTrace_5513200 : CollatzResearch.WordTrace tailWord_5513200 prefixEnd_5513200 2830921544367934813345261 := by
  unfold tailWord_5513200
  simp only [CollatzResearch.WordTrace]
  refine ⟨100541461813312727221064527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134055282417750302961419369 100541461813312727221064527)
  ·
    refine ⟨150812192719969090831596791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100541461813312727221064527 150812192719969090831596791)
    ·
      refine ⟨226218289079953636247395187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150812192719969090831596791 226218289079953636247395187)
      ·
        refine ⟨339327433619930454371092781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226218289079953636247395187 339327433619930454371092781)
        ·
          refine ⟨127247787607473920389159793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339327433619930454371092781 127247787607473920389159793)
          ·
            refine ⟨95435840705605440291869845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127247787607473920389159793 95435840705605440291869845)
            ·
              refine ⟨4473555033075255013681399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95435840705605440291869845 4473555033075255013681399)
              ·
                refine ⟨6710332549612882520522099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473555033075255013681399 6710332549612882520522099)
                ·
                  refine ⟨10065498824419323780783149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6710332549612882520522099 10065498824419323780783149)
                  ·
                    refine ⟨3774562059157246417793681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10065498824419323780783149 3774562059157246417793681)
                    ·
                      refine ⟨2830921544367934813345261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774562059157246417793681 2830921544367934813345261)
                      ·
                        rfl

theorem cell23_5513200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 3, 2].length) (baseStart_5513200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513200 prefixEnd_5513200 := by exact prefixLift 5513200
  have htrace : WordTrace (prefixWord ++ tailWord_5513200) baseStart_5513200 baseEnd_5513200 := by
    simpa [prefixWord, tailWord_5513200, baseEnd_5513200] using wordTrace_append hprefix tailTrace_5513200
  have hstable : (prefixWord ++ tailWord_5513200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513200).length < 2 ^ (prefixWord ++ tailWord_5513200).sum := by decide
  have hdescent : baseEnd_5513200 < baseStart_5513200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513253 : List Nat := [1, 3, 1, 2, 2, 3, 3, 3, 5]
def baseStart_5513253 : Nat := 118140960795 + 5513253 * 2 ^ 59
def prefixEnd_5513253 : Nat := 4983230072969 + 3 ^ 40 * 5513253 * 2
def baseEnd_5513253 : Nat := 314549862093624789553613

theorem tailTrace_5513253 : CollatzResearch.WordTrace tailWord_5513253 prefixEnd_5513253 314549862093624789553613 := by
  unfold tailWord_5513253
  simp only [CollatzResearch.WordTrace]
  refine ⟨201084856695433444493808413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134056571130288962995872275 201084856695433444493808413)
  ·
    refine ⟨75406821260787541685178155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201084856695433444493808413 75406821260787541685178155)
    ·
      refine ⟨113110231891181312527767233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75406821260787541685178155 113110231891181312527767233)
      ·
        refine ⟨84832673918385984395825425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113110231891181312527767233 84832673918385984395825425)
        ·
          refine ⟨63624505438789488296869069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84832673918385984395825425 63624505438789488296869069)
          ·
            refine ⟨23859189539546058111325901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63624505438789488296869069 23859189539546058111325901)
            ·
              refine ⟨8947196077329771791747213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23859189539546058111325901 8947196077329771791747213)
              ·
                refine ⟨3355198528998664421905205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8947196077329771791747213 3355198528998664421905205)
                ·
                  refine ⟨314549862093624789553613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3355198528998664421905205 314549862093624789553613)
                  ·
                    rfl

theorem cell23_5513253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_5513253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513253 prefixEnd_5513253 := by exact prefixLift 5513253
  have htrace : WordTrace (prefixWord ++ tailWord_5513253) baseStart_5513253 baseEnd_5513253 := by
    simpa [prefixWord, tailWord_5513253, baseEnd_5513253] using wordTrace_append hprefix tailTrace_5513253
  have hstable : (prefixWord ++ tailWord_5513253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513253).length < 2 ^ (prefixWord ++ tailWord_5513253).sum := by decide
  have hdescent : baseEnd_5513253 < baseStart_5513253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513266 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_5513266 : Nat := 118140960795 + 5513266 * 2 ^ 59
def prefixEnd_5513266 : Nat := 4983230072969 + 3 ^ 40 * 5513266 * 2
def baseEnd_5513266 : Nat := 943651811363710518373319

theorem tailTrace_5513266 : CollatzResearch.WordTrace tailWord_5513266 prefixEnd_5513266 943651811363710518373319 := by
  unfold tailWord_5513266
  simp only [CollatzResearch.WordTrace]
  refine ⟨50271332711096586928507913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134056887229590898476021101 50271332711096586928507913)
  ·
    refine ⟨37703499533322440196380935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50271332711096586928507913 37703499533322440196380935)
    ·
      refine ⟨56555249299983660294571403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37703499533322440196380935 56555249299983660294571403)
      ·
        refine ⟨84832873949975490441857105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56555249299983660294571403 84832873949975490441857105)
        ·
          refine ⟨63624655462481617831392829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84832873949975490441857105 63624655462481617831392829)
          ·
            refine ⟨23859245798430606686772311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63624655462481617831392829 23859245798430606686772311)
            ·
              refine ⟨35788868697645910030158467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23859245798430606686772311 35788868697645910030158467)
              ·
                refine ⟨53683303046468865045237701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35788868697645910030158467 53683303046468865045237701)
                ·
                  refine ⟨10065619321212912195982069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53683303046468865045237701 10065619321212912195982069)
                  ·
                    refine ⟨943651811363710518373319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10065619321212912195982069 943651811363710518373319)
                    ·
                      rfl

theorem cell23_5513266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_5513266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513266 prefixEnd_5513266 := by exact prefixLift 5513266
  have htrace : WordTrace (prefixWord ++ tailWord_5513266) baseStart_5513266 baseEnd_5513266 := by
    simpa [prefixWord, tailWord_5513266, baseEnd_5513266] using wordTrace_append hprefix tailTrace_5513266
  have hstable : (prefixWord ++ tailWord_5513266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513266).length < 2 ^ (prefixWord ++ tailWord_5513266).sum := by decide
  have hdescent : baseEnd_5513266 < baseStart_5513266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513276 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_5513276 : Nat := 118140960795 + 5513276 * 2 ^ 59
def prefixEnd_5513276 : Nat := 4983230072969 + 3 ^ 40 * 5513276 * 2
def baseEnd_5513276 : Nat := 2830960568897676515994911

theorem tailTrace_5513276 : CollatzResearch.WordTrace tailWord_5513276 prefixEnd_5513276 2830960568897676515994911 := by
  unfold tailWord_5513276
  simp only [CollatzResearch.WordTrace]
  refine ⟨100542847787175059710947841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134057130382900079614597121 100542847787175059710947841)
  ·
    refine ⟨75407135840381294783210881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100542847787175059710947841 75407135840381294783210881)
    ·
      refine ⟨56555351880285971087408161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75407135840381294783210881 56555351880285971087408161)
      ·
        refine ⟨42416513910214478315556121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56555351880285971087408161 42416513910214478315556121)
        ·
          refine ⟨31812385432660858736667091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42416513910214478315556121 31812385432660858736667091)
          ·
            refine ⟨47718578148991288105000637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31812385432660858736667091 47718578148991288105000637)
            ·
              refine ⟨17894466805871733039375239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47718578148991288105000637 17894466805871733039375239)
              ·
                refine ⟨26841700208807599559062859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17894466805871733039375239 26841700208807599559062859)
                ·
                  refine ⟨40262550313211399338594289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26841700208807599559062859 40262550313211399338594289)
                  ·
                    refine ⟨30196912734908549503945717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40262550313211399338594289 30196912734908549503945717)
                    ·
                      refine ⟨2830960568897676515994911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30196912734908549503945717 2830960568897676515994911)
                      ·
                        rfl

theorem cell23_5513276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_5513276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513276 prefixEnd_5513276 := by exact prefixLift 5513276
  have htrace : WordTrace (prefixWord ++ tailWord_5513276) baseStart_5513276 baseEnd_5513276 := by
    simpa [prefixWord, tailWord_5513276, baseEnd_5513276] using wordTrace_append hprefix tailTrace_5513276
  have hstable : (prefixWord ++ tailWord_5513276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513276).length < 2 ^ (prefixWord ++ tailWord_5513276).sum := by decide
  have hdescent : baseEnd_5513276 < baseStart_5513276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513336 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_5513336 : Nat := 118140960795 + 5513336 * 2 ^ 59
def prefixEnd_5513336 : Nat := 4983230072969 + 3 ^ 40 * 5513336 * 2
def baseEnd_5513336 : Nat := 2830991377736946281244635

theorem tailTrace_5513336 : CollatzResearch.WordTrace tailWord_5513336 prefixEnd_5513336 2830991377736946281244635 := by
  unfold tailWord_5513336
  simp only [CollatzResearch.WordTrace]
  refine ⟨100543941977066374834539931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134058589302755166446053241 100543941977066374834539931)
  ·
    refine ⟨150815912965599562251809897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100543941977066374834539931 150815912965599562251809897)
    ·
      refine ⟨113111934724199671688857423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150815912965599562251809897 113111934724199671688857423)
      ·
        refine ⟨169667902086299507533286135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113111934724199671688857423 169667902086299507533286135)
        ·
          refine ⟨254501853129449261299929203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169667902086299507533286135 254501853129449261299929203)
          ·
            refine ⟨381752779694173891949893805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254501853129449261299929203 381752779694173891949893805)
            ·
              refine ⟨143157292385315209481210177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381752779694173891949893805 143157292385315209481210177)
              ·
                refine ⟨107367969288986407110907633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143157292385315209481210177 107367969288986407110907633)
                ·
                  refine ⟨80525976966739805333180725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107367969288986407110907633 80525976966739805333180725)
                  ·
                    refine ⟨7549310340631856749985693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80525976966739805333180725 7549310340631856749985693)
                    ·
                      refine ⟨2830991377736946281244635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7549310340631856749985693 2830991377736946281244635)
                      ·
                        rfl

theorem cell23_5513336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_5513336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513336 prefixEnd_5513336 := by exact prefixLift 5513336
  have htrace : WordTrace (prefixWord ++ tailWord_5513336) baseStart_5513336 baseEnd_5513336 := by
    simpa [prefixWord, tailWord_5513336, baseEnd_5513336] using wordTrace_append hprefix tailTrace_5513336
  have hstable : (prefixWord ++ tailWord_5513336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513336).length < 2 ^ (prefixWord ++ tailWord_5513336).sum := by decide
  have hdescent : baseEnd_5513336 < baseStart_5513336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513413 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_5513413 : Nat := 118140960795 + 5513413 * 2 ^ 59
def prefixEnd_5513413 : Nat := 4983230072969 + 3 ^ 40 * 5513413 * 2
def baseEnd_5513413 : Nat := 2831030915747342479981781

theorem tailTrace_5513413 : CollatzResearch.WordTrace tailWord_5513413 prefixEnd_5513413 2831030915747342479981781 := by
  unfold tailWord_5513413
  simp only [CollatzResearch.WordTrace]
  refine ⟨201090692374853791819632893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134060461583235861213088595 201090692374853791819632893)
  ·
    refine ⟨75409009640570171932362335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201090692374853791819632893 75409009640570171932362335)
    ·
      refine ⟨113113514460855257898543503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75409009640570171932362335 113113514460855257898543503)
      ·
        refine ⟨169670271691282886847815255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113113514460855257898543503 169670271691282886847815255)
        ·
          refine ⟨254505407536924330271722883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169670271691282886847815255 254505407536924330271722883)
          ·
            refine ⟨381758111305386495407584325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254505407536924330271722883 381758111305386495407584325)
            ·
              refine ⟨71579645869759967888922061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 381758111305386495407584325 71579645869759967888922061)
              ·
                refine ⟨26842367201159987958345773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71579645869759967888922061 26842367201159987958345773)
                ·
                  refine ⟨10065887700434995484379665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26842367201159987958345773 10065887700434995484379665)
                  ·
                    refine ⟨7549415775326246613284749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10065887700434995484379665 7549415775326246613284749)
                    ·
                      refine ⟨2831030915747342479981781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7549415775326246613284749 2831030915747342479981781)
                      ·
                        rfl

theorem cell23_5513413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_5513413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513413 prefixEnd_5513413 := by exact prefixLift 5513413
  have htrace : WordTrace (prefixWord ++ tailWord_5513413) baseStart_5513413 baseEnd_5513413 := by
    simpa [prefixWord, tailWord_5513413, baseEnd_5513413] using wordTrace_append hprefix tailTrace_5513413
  have hstable : (prefixWord ++ tailWord_5513413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513413).length < 2 ^ (prefixWord ++ tailWord_5513413).sum := by decide
  have hdescent : baseEnd_5513413 < baseStart_5513413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513500 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_5513500 : Nat := 118140960795 + 5513500 * 2 ^ 59
def prefixEnd_5513500 : Nat := 4983230072969 + 3 ^ 40 * 5513500 * 2
def baseEnd_5513500 : Nat := 2831075588564283639593881

theorem tailTrace_5513500 : CollatzResearch.WordTrace tailWord_5513500 prefixEnd_5513500 2831075588564283639593881 := by
  unfold tailWord_5513500
  simp only [CollatzResearch.WordTrace]
  refine ⟨100546932762769302839024977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134062577017025737118699969 100546932762769302839024977)
  ·
    refine ⟨75410199572076977129268733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100546932762769302839024977 75410199572076977129268733)
    ·
      refine ⟨28278824839528866423475775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75410199572076977129268733 28278824839528866423475775)
      ·
        refine ⟨42418237259293299635213663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28278824839528866423475775 42418237259293299635213663)
        ·
          refine ⟨63627355888939949452820495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42418237259293299635213663 63627355888939949452820495)
          ·
            refine ⟨95441033833409924179230743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63627355888939949452820495 95441033833409924179230743)
            ·
              refine ⟨143161550750114886268846115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95441033833409924179230743 143161550750114886268846115)
              ·
                refine ⟨214742326125172329403269173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143161550750114886268846115 214742326125172329403269173)
                ·
                  refine ⟨20132093074234905881556485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214742326125172329403269173 20132093074234905881556485)
                  ·
                    refine ⟨3774767451419044852791841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20132093074234905881556485 3774767451419044852791841)
                    ·
                      refine ⟨2831075588564283639593881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774767451419044852791841 2831075588564283639593881)
                      ·
                        rfl

theorem cell23_5513500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_5513500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513500 prefixEnd_5513500 := by exact prefixLift 5513500
  have htrace : WordTrace (prefixWord ++ tailWord_5513500) baseStart_5513500 baseEnd_5513500 := by
    simpa [prefixWord, tailWord_5513500, baseEnd_5513500] using wordTrace_append hprefix tailTrace_5513500
  have hstable : (prefixWord ++ tailWord_5513500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513500).length < 2 ^ (prefixWord ++ tailWord_5513500).sum := by decide
  have hdescent : baseEnd_5513500 < baseStart_5513500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513511 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5513511 : Nat := 118140960795 + 5513511 * 2 ^ 59
def prefixEnd_5513511 : Nat := 4983230072969 + 3 ^ 40 * 5513511 * 2
def baseEnd_5513511 : Nat := 2831081236851483096556331

theorem tailTrace_5513511 : CollatzResearch.WordTrace tailWord_5513511 prefixEnd_5513511 2831081236851483096556331 := by
  unfold tailWord_5513511
  simp only [CollatzResearch.WordTrace]
  refine ⟨201094266728498754556700387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134062844485665836371133591 201094266728498754556700387)
  ·
    refine ⟨301641400092748131835050581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201094266728498754556700387 301641400092748131835050581)
    ·
      refine ⟨3534860157336892169941999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 301641400092748131835050581 3534860157336892169941999)
      ·
        refine ⟨5302290236005338254912999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534860157336892169941999 5302290236005338254912999)
        ·
          refine ⟨7953435354008007382369499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5302290236005338254912999 7953435354008007382369499)
          ·
            refine ⟨11930153031012011073554249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7953435354008007382369499 11930153031012011073554249)
            ·
              refine ⟨8947614773259008305165687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11930153031012011073554249 8947614773259008305165687)
              ·
                refine ⟨13421422159888512457748531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8947614773259008305165687 13421422159888512457748531)
                ·
                  refine ⟨20132133239832768686622797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13421422159888512457748531 20132133239832768686622797)
                  ·
                    refine ⟨7549549964937288257483549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20132133239832768686622797 7549549964937288257483549)
                    ·
                      refine ⟨2831081236851483096556331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7549549964937288257483549 2831081236851483096556331)
                      ·
                        rfl

theorem cell23_5513511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5513511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513511 prefixEnd_5513511 := by exact prefixLift 5513511
  have htrace : WordTrace (prefixWord ++ tailWord_5513511) baseStart_5513511 baseEnd_5513511 := by
    simpa [prefixWord, tailWord_5513511, baseEnd_5513511] using wordTrace_append hprefix tailTrace_5513511
  have hstable : (prefixWord ++ tailWord_5513511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513511).length < 2 ^ (prefixWord ++ tailWord_5513511).sum := by decide
  have hdescent : baseEnd_5513511 < baseStart_5513511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513523 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 7]
def baseStart_5513523 : Nat := 118140960795 + 5513523 * 2 ^ 59
def prefixEnd_5513523 : Nat := 4983230072969 + 3 ^ 40 * 5513523 * 2
def baseEnd_5513523 : Nat := 314565266513259672178475

theorem tailTrace_5513523 : CollatzResearch.WordTrace tailWord_5513523 prefixEnd_5513523 314565266513259672178475 := by
  unfold tailWord_5513523
  simp only [CollatzResearch.WordTrace]
  refine ⟨201094704404455280606137223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134063136269636853737424815 201094704404455280606137223)
  ·
    refine ⟨301642056606682920909205835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201094704404455280606137223 301642056606682920909205835)
    ·
      refine ⟨452463084910024381363808753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301642056606682920909205835 452463084910024381363808753)
      ·
        refine ⟨339347313682518286022856565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452463084910024381363808753 339347313682518286022856565)
        ·
          refine ⟨31813810657736089314642803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 339347313682518286022856565 31813810657736089314642803)
          ·
            refine ⟨47720715986604133971964205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31813810657736089314642803 47720715986604133971964205)
            ·
              refine ⟨17895268494976550239486577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47720715986604133971964205 17895268494976550239486577)
              ·
                refine ⟨13421451371232412679614933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17895268494976550239486577 13421451371232412679614933)
                ·
                  refine ⟨314565266513259672178475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13421451371232412679614933 314565266513259672178475)
                  ·
                    rfl

theorem cell23_5513523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 7].length) (baseStart_5513523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513523 prefixEnd_5513523 := by exact prefixLift 5513523
  have htrace : WordTrace (prefixWord ++ tailWord_5513523) baseStart_5513523 baseEnd_5513523 := by
    simpa [prefixWord, tailWord_5513523, baseEnd_5513523] using wordTrace_append hprefix tailTrace_5513523
  have hstable : (prefixWord ++ tailWord_5513523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513523).length < 2 ^ (prefixWord ++ tailWord_5513523).sum := by decide
  have hdescent : baseEnd_5513523 < baseStart_5513523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513560 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 2, 5, 2]
def baseStart_5513560 : Nat := 118140960795 + 5513560 * 2 ^ 59
def prefixEnd_5513560 : Nat := 4983230072969 + 3 ^ 40 * 5513560 * 2
def baseEnd_5513560 : Nat := 2831106397403553404843605

theorem tailTrace_5513560 : CollatzResearch.WordTrace tailWord_5513560 prefixEnd_5513560 2831106397403553404843605 := by
  unfold tailWord_5513560
  simp only [CollatzResearch.WordTrace]
  refine ⟨100548026952660617962617067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134064035936880823950156089 100548026952660617962617067)
  ·
    refine ⟨150822040428990926943925601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100548026952660617962617067 150822040428990926943925601)
    ·
      refine ⟨113116530321743195207944201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150822040428990926943925601 113116530321743195207944201)
      ·
        refine ⟨84837397741307396405958151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113116530321743195207944201 84837397741307396405958151)
        ·
          refine ⟨127256096611961094608937227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84837397741307396405958151 127256096611961094608937227)
          ·
            refine ⟨190884144917941641913405841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127256096611961094608937227 190884144917941641913405841)
            ·
              refine ⟨143163108688456231435054381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190884144917941641913405841 143163108688456231435054381)
              ·
                refine ⟨53686165758171086788145393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143163108688456231435054381 53686165758171086788145393)
                ·
                  refine ⟨40264624318628315091109045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53686165758171086788145393 40264624318628315091109045)
                  ·
                    refine ⟨3774808529871404539791473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40264624318628315091109045 3774808529871404539791473)
                    ·
                      refine ⟨2831106397403553404843605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774808529871404539791473 2831106397403553404843605)
                      ·
                        rfl

theorem cell23_5513560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_5513560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513560 prefixEnd_5513560 := by exact prefixLift 5513560
  have htrace : WordTrace (prefixWord ++ tailWord_5513560) baseStart_5513560 baseEnd_5513560 := by
    simpa [prefixWord, tailWord_5513560, baseEnd_5513560] using wordTrace_append hprefix tailTrace_5513560
  have hstable : (prefixWord ++ tailWord_5513560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513560).length < 2 ^ (prefixWord ++ tailWord_5513560).sum := by decide
  have hdescent : baseEnd_5513560 < baseStart_5513560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513570 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_5513570 : Nat := 118140960795 + 5513570 * 2 ^ 59
def prefixEnd_5513570 : Nat := 4983230072969 + 3 ^ 40 * 5513570 * 2
def baseEnd_5513570 : Nat := 943703844070032788572853

theorem tailTrace_5513570 : CollatzResearch.WordTrace tailWord_5513570 prefixEnd_5513570 943703844070032788572853 := by
  unfold tailWord_5513570
  simp only [CollatzResearch.WordTrace]
  refine ⟨50274104658821251908274541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134064279090190005088732109 50274104658821251908274541)
  ·
    refine ⟨18852789247057969465602953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50274104658821251908274541 18852789247057969465602953)
    ·
      refine ⟨14139591935293477099202215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18852789247057969465602953 14139591935293477099202215)
      ·
        refine ⟨21209387902940215648803323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14139591935293477099202215 21209387902940215648803323)
        ·
          refine ⟨31814081854410323473204985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21209387902940215648803323 31814081854410323473204985)
          ·
            refine ⟨23860561390807742604903739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31814081854410323473204985 23860561390807742604903739)
            ·
              refine ⟨35790842086211613907355609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23860561390807742604903739 35790842086211613907355609)
              ·
                refine ⟨26843131564658710430516707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35790842086211613907355609 26843131564658710430516707)
                ·
                  refine ⟨40264697346988065645775061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26843131564658710430516707 40264697346988065645775061)
                  ·
                    refine ⟨943703844070032788572853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40264697346988065645775061 943703844070032788572853)
                    ·
                      rfl

theorem cell23_5513570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_5513570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513570 prefixEnd_5513570 := by exact prefixLift 5513570
  have htrace : WordTrace (prefixWord ++ tailWord_5513570) baseStart_5513570 baseEnd_5513570 := by
    simpa [prefixWord, tailWord_5513570, baseEnd_5513570] using wordTrace_append hprefix tailTrace_5513570
  have hstable : (prefixWord ++ tailWord_5513570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513570).length < 2 ^ (prefixWord ++ tailWord_5513570).sum := by decide
  have hdescent : baseEnd_5513570 < baseStart_5513570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513593 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_5513593 : Nat := 118140960795 + 5513593 * 2 ^ 59
def prefixEnd_5513593 : Nat := 4983230072969 + 3 ^ 40 * 5513593 * 2
def baseEnd_5513593 : Nat := 2831123342265151775730953

theorem tailTrace_5513593 : CollatzResearch.WordTrace tailWord_5513593 prefixEnd_5513593 2831123342265151775730953 := by
  unfold tailWord_5513593
  simp only [CollatzResearch.WordTrace]
  refine ⟨201097257514201682561185433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134064838342801121707456955 201097257514201682561185433)
  ·
    refine ⟨150822943135651261920889075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201097257514201682561185433 150822943135651261920889075)
    ·
      refine ⟨226234414703476892881333613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150822943135651261920889075 226234414703476892881333613)
      ·
        refine ⟨84837905513803834830500105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226234414703476892881333613 84837905513803834830500105)
        ·
          refine ⟨63628429135352876122875079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84837905513803834830500105 63628429135352876122875079)
          ·
            refine ⟨95442643703029314184312619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63628429135352876122875079 95442643703029314184312619)
            ·
              refine ⟨143163965554543971276468929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95442643703029314184312619 143163965554543971276468929)
              ·
                refine ⟨107372974165907978457351697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143163965554543971276468929 107372974165907978457351697)
                ·
                  refine ⟨80529730624430983843013773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107372974165907978457351697 80529730624430983843013773)
                  ·
                    refine ⟨30198648984161618941130165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80529730624430983843013773 30198648984161618941130165)
                    ·
                      refine ⟨2831123342265151775730953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30198648984161618941130165 2831123342265151775730953)
                      ·
                        rfl

theorem cell23_5513593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_5513593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513593 prefixEnd_5513593 := by exact prefixLift 5513593
  have htrace : WordTrace (prefixWord ++ tailWord_5513593) baseStart_5513593 baseEnd_5513593 := by
    simpa [prefixWord, tailWord_5513593, baseEnd_5513593] using wordTrace_append hprefix tailTrace_5513593
  have hstable : (prefixWord ++ tailWord_5513593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513593).length < 2 ^ (prefixWord ++ tailWord_5513593).sum := by decide
  have hdescent : baseEnd_5513593 < baseStart_5513593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513697 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_5513697 : Nat := 118140960795 + 5513697 * 2 ^ 59
def prefixEnd_5513697 : Nat := 4983230072969 + 3 ^ 40 * 5513697 * 2
def baseEnd_5513697 : Nat := 2831176744253219368830475

theorem tailTrace_5513697 : CollatzResearch.WordTrace tailWord_5513697 prefixEnd_5513697 2831176744253219368830475 := by
  unfold tailWord_5513697
  simp only [CollatzResearch.WordTrace]
  refine ⟨201101050705824908322971345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134067367137216605548647563 201101050705824908322971345)
  ·
    refine ⟨150825788029368681242228509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201101050705824908322971345 150825788029368681242228509)
    ·
      refine ⟨56559670511013255465835691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150825788029368681242228509 56559670511013255465835691)
      ·
        refine ⟨84839505766519883198753537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56559670511013255465835691 84839505766519883198753537)
        ·
          refine ⟨63629629324889912399065153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84839505766519883198753537 63629629324889912399065153)
          ·
            refine ⟨47722221993667434299298865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63629629324889912399065153 47722221993667434299298865)
            ·
              refine ⟨35791666495250575724474149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47722221993667434299298865 35791666495250575724474149)
              ·
                refine ⟨6710937467859482948338903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35791666495250575724474149 6710937467859482948338903)
                ·
                  refine ⟨10066406201789224422508355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6710937467859482948338903 10066406201789224422508355)
                  ·
                    refine ⟨15099609302683836633762533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10066406201789224422508355 15099609302683836633762533)
                    ·
                      refine ⟨2831176744253219368830475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15099609302683836633762533 2831176744253219368830475)
                      ·
                        rfl

theorem cell23_5513697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_5513697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513697 prefixEnd_5513697 := by exact prefixLift 5513697
  have htrace : WordTrace (prefixWord ++ tailWord_5513697) baseStart_5513697 baseEnd_5513697 := by
    simpa [prefixWord, tailWord_5513697, baseEnd_5513697] using wordTrace_append hprefix tailTrace_5513697
  have hstable : (prefixWord ++ tailWord_5513697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513697).length < 2 ^ (prefixWord ++ tailWord_5513697).sum := by decide
  have hdescent : baseEnd_5513697 < baseStart_5513697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513731 : List Nat := [1, 1, 1, 3, 2, 1, 3, 6, 1, 2, 2]
def baseStart_5513731 : Nat := 118140960795 + 5513731 * 2 ^ 59
def prefixEnd_5513731 : Nat := 4983230072969 + 3 ^ 40 * 5513731 * 2
def baseEnd_5513731 : Nat := 2831194202595472235805319

theorem tailTrace_5513731 : CollatzResearch.WordTrace tailWord_5513731 prefixEnd_5513731 2831194202595472235805319 := by
  unfold tailWord_5513731
  simp only [CollatzResearch.WordTrace]
  refine ⟨201102290787701732129709047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134068193858467821419806031 201102290787701732129709047)
  ·
    refine ⟨301653436181552598194563571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201102290787701732129709047 301653436181552598194563571)
    ·
      refine ⟨452480154272328897291845357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301653436181552598194563571 452480154272328897291845357)
      ·
        refine ⟨169680057852123336484442009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 452480154272328897291845357 169680057852123336484442009)
        ·
          refine ⟨127260043389092502363331507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169680057852123336484442009 127260043389092502363331507)
          ·
            refine ⟨190890065083638753544997261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127260043389092502363331507 190890065083638753544997261)
            ·
              refine ⟨71583774406364532579373973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190890065083638753544997261 71583774406364532579373973)
              ·
                refine ⟨3355489425298337464658155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71583774406364532579373973 3355489425298337464658155)
                ·
                  refine ⟨5033234137947506196987233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355489425298337464658155 5033234137947506196987233)
                  ·
                    refine ⟨3774925603460629647740425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5033234137947506196987233 3774925603460629647740425)
                    ·
                      refine ⟨2831194202595472235805319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774925603460629647740425 2831194202595472235805319)
                      ·
                        rfl

theorem cell23_5513731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_5513731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513731 prefixEnd_5513731 := by exact prefixLift 5513731
  have htrace : WordTrace (prefixWord ++ tailWord_5513731) baseStart_5513731 baseEnd_5513731 := by
    simpa [prefixWord, tailWord_5513731, baseEnd_5513731] using wordTrace_append hprefix tailTrace_5513731
  have hstable : (prefixWord ++ tailWord_5513731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513731).length < 2 ^ (prefixWord ++ tailWord_5513731).sum := by decide
  have hdescent : baseEnd_5513731 < baseStart_5513731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513741 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_5513741 : Nat := 118140960795 + 5513741 * 2 ^ 59
def prefixEnd_5513741 : Nat := 4983230072969 + 3 ^ 40 * 5513741 * 2
def baseEnd_5513741 : Nat := 943733112467339065560091

theorem tailTrace_5513741 : CollatzResearch.WordTrace tailWord_5513741 prefixEnd_5513741 943733112467339065560091 := by
  unfold tailWord_5513741
  simp only [CollatzResearch.WordTrace]
  refine ⟨201102655517665503837573077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134068437011777002558382051 201102655517665503837573077)
  ·
    refine ⟨4713343488695285246193119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 201102655517665503837573077 4713343488695285246193119)
    ·
      refine ⟨7070015233042927869289679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4713343488695285246193119 7070015233042927869289679)
      ·
        refine ⟨10605022849564391803934519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7070015233042927869289679 10605022849564391803934519)
        ·
          refine ⟨15907534274346587705901779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10605022849564391803934519 15907534274346587705901779)
          ·
            refine ⟨23861301411519881558852669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15907534274346587705901779 23861301411519881558852669)
            ·
              refine ⟨8947988029319955584569751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23861301411519881558852669 8947988029319955584569751)
              ·
                refine ⟨13421982043979933376854627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8947988029319955584569751 13421982043979933376854627)
                ·
                  refine ⟨20132973065969900065281941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13421982043979933376854627 20132973065969900065281941)
                  ·
                    refine ⟨943733112467339065560091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20132973065969900065281941 943733112467339065560091)
                    ·
                      rfl

theorem cell23_5513741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_5513741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513741 prefixEnd_5513741 := by exact prefixLift 5513741
  have htrace : WordTrace (prefixWord ++ tailWord_5513741) baseStart_5513741 baseEnd_5513741 := by
    simpa [prefixWord, tailWord_5513741, baseEnd_5513741] using wordTrace_append hprefix tailTrace_5513741
  have hstable : (prefixWord ++ tailWord_5513741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513741).length < 2 ^ (prefixWord ++ tailWord_5513741).sum := by decide
  have hdescent : baseEnd_5513741 < baseStart_5513741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513748 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5513748 : Nat := 118140960795 + 5513748 * 2 ^ 59
def prefixEnd_5513748 : Nat := 4983230072969 + 3 ^ 40 * 5513748 * 2
def baseEnd_5513748 : Nat := 2831202931766598669292741

theorem tailTrace_5513748 : CollatzResearch.WordTrace tailWord_5513748 prefixEnd_5513748 2831202931766598669292741 := by
  unfold tailWord_5513748
  simp only [CollatzResearch.WordTrace]
  refine ⟨100551455414320072016538949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134068607219093429355385265 100551455414320072016538949)
  ·
    refine ⟨18853397890185013503101053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100551455414320072016538949 18853397890185013503101053)
    ·
      refine ⟨7070024208819380063662895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18853397890185013503101053 7070024208819380063662895)
      ·
        refine ⟨10605036313229070095494343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7070024208819380063662895 10605036313229070095494343)
        ·
          refine ⟨15907554469843605143241515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10605036313229070095494343 15907554469843605143241515)
          ·
            refine ⟨23861331704765407714862273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15907554469843605143241515 23861331704765407714862273)
            ·
              refine ⟨17895998778574055786146705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23861331704765407714862273 17895998778574055786146705)
              ·
                refine ⟨13421999083930541839610029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17895998778574055786146705 13421999083930541839610029)
                ·
                  refine ⟨5033249656473953189853761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13421999083930541839610029 5033249656473953189853761)
                  ·
                    refine ⟨3774937242355464892390321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5033249656473953189853761 3774937242355464892390321)
                    ·
                      refine ⟨2831202931766598669292741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774937242355464892390321 2831202931766598669292741)
                      ·
                        rfl

theorem cell23_5513748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5513748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513748 prefixEnd_5513748 := by exact prefixLift 5513748
  have htrace : WordTrace (prefixWord ++ tailWord_5513748) baseStart_5513748 baseEnd_5513748 := by
    simpa [prefixWord, tailWord_5513748, baseEnd_5513748] using wordTrace_append hprefix tailTrace_5513748
  have hstable : (prefixWord ++ tailWord_5513748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513748).length < 2 ^ (prefixWord ++ tailWord_5513748).sum := by decide
  have hdescent : baseEnd_5513748 < baseStart_5513748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513782 : List Nat := [5, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_5513782 : Nat := 118140960795 + 5513782 * 2 ^ 59
def prefixEnd_5513782 : Nat := 4983230072969 + 3 ^ 40 * 5513782 * 2
def baseEnd_5513782 : Nat := 2831220390108851536267585

theorem tailTrace_5513782 : CollatzResearch.WordTrace tailWord_5513782 prefixEnd_5513782 2831220390108851536267585 := by
  unfold tailWord_5513782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12569009431907310489988475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134069433940344645226543733 12569009431907310489988475)
  ·
    refine ⟨18853514147860965734982713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12569009431907310489988475 18853514147860965734982713)
    ·
      refine ⟨14140135610895724301237035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18853514147860965734982713 14140135610895724301237035)
      ·
        refine ⟨21210203416343586451855553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14140135610895724301237035 21210203416343586451855553)
        ·
          refine ⟨15907652562257689838891665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21210203416343586451855553 15907652562257689838891665)
          ·
            refine ⟨11930739421693267379168749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15907652562257689838891665 11930739421693267379168749)
            ·
              refine ⟨4474027283134975267188281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11930739421693267379168749 4474027283134975267188281)
              ·
                refine ⟨3355520462351231450391211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474027283134975267188281 3355520462351231450391211)
                ·
                  refine ⟨5033280693526847175586817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355520462351231450391211 5033280693526847175586817)
                  ·
                    refine ⟨3774960520145135381690113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5033280693526847175586817 3774960520145135381690113)
                    ·
                      refine ⟨2831220390108851536267585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774960520145135381690113 2831220390108851536267585)
                      ·
                        rfl

theorem cell23_5513782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_5513782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513782 prefixEnd_5513782 := by exact prefixLift 5513782
  have htrace : WordTrace (prefixWord ++ tailWord_5513782) baseStart_5513782 baseEnd_5513782 := by
    simpa [prefixWord, tailWord_5513782, baseEnd_5513782] using wordTrace_append hprefix tailTrace_5513782
  have hstable : (prefixWord ++ tailWord_5513782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513782).length < 2 ^ (prefixWord ++ tailWord_5513782).sum := by decide
  have hdescent : baseEnd_5513782 < baseStart_5513782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513800 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_5513800 : Nat := 118140960795 + 5513800 * 2 ^ 59
def prefixEnd_5513800 : Nat := 4983230072969 + 3 ^ 40 * 5513800 * 2
def baseEnd_5513800 : Nat := 2831229632760632465842501

theorem tailTrace_5513800 : CollatzResearch.WordTrace tailWord_5513800 prefixEnd_5513800 2831229632760632465842501 := by
  unfold tailWord_5513800
  simp only [CollatzResearch.WordTrace]
  refine ⟨100552403712225878456985427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134069871616301171275980569 100552403712225878456985427)
  ·
    refine ⟨150828605568338817685478141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100552403712225878456985427 150828605568338817685478141)
    ·
      refine ⟨56560727088127056632054303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150828605568338817685478141 56560727088127056632054303)
      ·
        refine ⟨84841090632190584948081455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56560727088127056632054303 84841090632190584948081455)
        ·
          refine ⟨127261635948285877422122183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84841090632190584948081455 127261635948285877422122183)
          ·
            refine ⟨190892453922428816133183275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127261635948285877422122183 190892453922428816133183275)
            ·
              refine ⟨286338680883643224199774913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190892453922428816133183275 286338680883643224199774913)
              ·
                refine ⟨214754010662732418149831185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286338680883643224199774913 214754010662732418149831185)
                ·
                  refine ⟨161065507997049313612373389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214754010662732418149831185 161065507997049313612373389)
                  ·
                    refine ⟨60399565498893492604640021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161065507997049313612373389 60399565498893492604640021)
                    ·
                      refine ⟨2831229632760632465842501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60399565498893492604640021 2831229632760632465842501)
                      ·
                        rfl

theorem cell23_5513800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_5513800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513800 prefixEnd_5513800 := by exact prefixLift 5513800
  have htrace : WordTrace (prefixWord ++ tailWord_5513800) baseStart_5513800 baseEnd_5513800 := by
    simpa [prefixWord, tailWord_5513800, baseEnd_5513800] using wordTrace_append hprefix tailTrace_5513800
  have hstable : (prefixWord ++ tailWord_5513800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513800).length < 2 ^ (prefixWord ++ tailWord_5513800).sum := by decide
  have hdescent : baseEnd_5513800 < baseStart_5513800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513804 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 1, 4, 2]
def baseStart_5513804 : Nat := 118140960795 + 5513804 * 2 ^ 59
def prefixEnd_5513804 : Nat := 4983230072969 + 3 ^ 40 * 5513804 * 2
def baseEnd_5513804 : Nat := 2831231686683250450192483

theorem tailTrace_5513804 : CollatzResearch.WordTrace tailWord_5513804 prefixEnd_5513804 2831231686683250450192483 := by
  unfold tailWord_5513804
  simp only [CollatzResearch.WordTrace]
  refine ⟨100552476658218632798558233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134069968877624843731410977 100552476658218632798558233)
  ·
    refine ⟨75414357493663974598918675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100552476658218632798558233 75414357493663974598918675)
    ·
      refine ⟨113121536240495961898378013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75414357493663974598918675 113121536240495961898378013)
      ·
        refine ⟨42420576090185985711891755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113121536240495961898378013 42420576090185985711891755)
        ·
          refine ⟨63630864135278978567837633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42420576090185985711891755 63630864135278978567837633)
          ·
            refine ⟨47723148101459233925878225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63630864135278978567837633 47723148101459233925878225)
            ·
              refine ⟨35792361076094425444408669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47723148101459233925878225 35792361076094425444408669)
              ·
                refine ⟨13422135403535409541653251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35792361076094425444408669 13422135403535409541653251)
                ·
                  refine ⟨20133203105303114312479877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13422135403535409541653251 20133203105303114312479877)
                  ·
                    refine ⟨3774975582244333933589977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20133203105303114312479877 3774975582244333933589977)
                    ·
                      refine ⟨2831231686683250450192483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774975582244333933589977 2831231686683250450192483)
                      ·
                        rfl

theorem cell23_5513804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_5513804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513804 prefixEnd_5513804 := by exact prefixLift 5513804
  have htrace : WordTrace (prefixWord ++ tailWord_5513804) baseStart_5513804 baseEnd_5513804 := by
    simpa [prefixWord, tailWord_5513804, baseEnd_5513804] using wordTrace_append hprefix tailTrace_5513804
  have hstable : (prefixWord ++ tailWord_5513804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513804).length < 2 ^ (prefixWord ++ tailWord_5513804).sum := by decide
  have hdescent : baseEnd_5513804 < baseStart_5513804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513838 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_5513838 : Nat := 118140960795 + 5513838 * 2 ^ 59
def prefixEnd_5513838 : Nat := 4983230072969 + 3 ^ 40 * 5513838 * 2
def baseEnd_5513838 : Nat := 2831249145025503317167327

theorem tailTrace_5513838 : CollatzResearch.WordTrace tailWord_5513838 prefixEnd_5513838 2831249145025503317167327 := by
  unfold tailWord_5513838
  simp only [CollatzResearch.WordTrace]
  refine ⟨25138274174789261175481771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134070795598876059602569445 25138274174789261175481771)
  ·
    refine ⟨37707411262183891763222657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25138274174789261175481771 37707411262183891763222657)
    ·
      refine ⟨28280558446637918822416993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37707411262183891763222657 28280558446637918822416993)
      ·
        refine ⟨21210418834978439116812745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28280558446637918822416993 21210418834978439116812745)
        ·
          refine ⟨15907814126233829337609559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21210418834978439116812745 15907814126233829337609559)
          ·
            refine ⟨23861721189350744006414339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15907814126233829337609559 23861721189350744006414339)
            ·
              refine ⟨35792581784026116009621509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23861721189350744006414339 35792581784026116009621509)
              ·
                refine ⟨6711109084504896751804033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35792581784026116009621509 6711109084504896751804033)
                ·
                  refine ⟨5033331813378672563853025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6711109084504896751804033 5033331813378672563853025)
                  ·
                    refine ⟨3774998860034004422889769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5033331813378672563853025 3774998860034004422889769)
                    ·
                      refine ⟨2831249145025503317167327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3774998860034004422889769 2831249145025503317167327)
                      ·
                        rfl

theorem cell23_5513838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_5513838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513838 prefixEnd_5513838 := by exact prefixLift 5513838
  have htrace : WordTrace (prefixWord ++ tailWord_5513838) baseStart_5513838 baseEnd_5513838 := by
    simpa [prefixWord, tailWord_5513838, baseEnd_5513838] using wordTrace_append hprefix tailTrace_5513838
  have hstable : (prefixWord ++ tailWord_5513838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513838).length < 2 ^ (prefixWord ++ tailWord_5513838).sum := by decide
  have hdescent : baseEnd_5513838 < baseStart_5513838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513857 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 1, 7]
def baseStart_5513857 : Nat := 118140960795 + 5513857 * 2 ^ 59
def prefixEnd_5513857 : Nat := 4983230072969 + 3 ^ 40 * 5513857 * 2
def baseEnd_5513857 : Nat := 943752967052646247609913

theorem tailTrace_5513857 : CollatzResearch.WordTrace tailWord_5513857 prefixEnd_5513857 943752967052646247609913 := by
  unfold tailWord_5513857
  simp only [CollatzResearch.WordTrace]
  refine ⟨201106886385245255648795825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134071257590163503765863883 201106886385245255648795825)
  ·
    refine ⟨150830164788933941736596869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201106886385245255648795825 150830164788933941736596869)
    ·
      refine ⟨28280655897925114075611913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150830164788933941736596869 28280655897925114075611913)
      ·
        refine ⟨21210491923443835556708935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28280655897925114075611913 21210491923443835556708935)
        ·
          refine ⟨31815737885165753335063403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21210491923443835556708935 31815737885165753335063403)
          ·
            refine ⟨47723606827748630002595105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31815737885165753335063403 47723606827748630002595105)
            ·
              refine ⟨35792705120811472501946329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47723606827748630002595105 35792705120811472501946329)
              ·
                refine ⟨26844528840608604376459747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35792705120811472501946329 26844528840608604376459747)
                ·
                  refine ⟨40266793260912906564689621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26844528840608604376459747 40266793260912906564689621)
                  ·
                    refine ⟨943752967052646247609913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40266793260912906564689621 943752967052646247609913)
                    ·
                      rfl

theorem cell23_5513857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_5513857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513857 prefixEnd_5513857 := by exact prefixLift 5513857
  have htrace : WordTrace (prefixWord ++ tailWord_5513857) baseStart_5513857 baseEnd_5513857 := by
    simpa [prefixWord, tailWord_5513857, baseEnd_5513857] using wordTrace_append hprefix tailTrace_5513857
  have hstable : (prefixWord ++ tailWord_5513857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513857).length < 2 ^ (prefixWord ++ tailWord_5513857).sum := by decide
  have hdescent : baseEnd_5513857 < baseStart_5513857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513874 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_5513874 : Nat := 118140960795 + 5513874 * 2 ^ 59
def prefixEnd_5513874 : Nat := 4983230072969 + 3 ^ 40 * 5513874 * 2
def baseEnd_5513874 : Nat := 943755876776355058772387

theorem tailTrace_5513874 : CollatzResearch.WordTrace tailWord_5513874 prefixEnd_5513874 943755876776355058772387 := by
  unfold tailWord_5513874
  simp only [CollatzResearch.WordTrace]
  refine ⟨50276876606545916888041169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134071670950789111701443117 50276876606545916888041169)
  ·
    refine ⟨37707657454909437666030877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50276876606545916888041169 37707657454909437666030877)
    ·
      refine ⟨14140371545591039124761579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37707657454909437666030877 14140371545591039124761579)
      ·
        refine ⟨21210557318386558687142369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14140371545591039124761579 21210557318386558687142369)
        ·
          refine ⟨15907917988789919015356777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21210557318386558687142369 15907917988789919015356777)
          ·
            refine ⟨11930938491592439261517583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15907917988789919015356777 11930938491592439261517583)
            ·
              refine ⟨17896407737388658892276375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11930938491592439261517583 17896407737388658892276375)
              ·
                refine ⟨26844611606082988338414563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17896407737388658892276375 26844611606082988338414563)
                ·
                  refine ⟨40266917409124482507621845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26844611606082988338414563 40266917409124482507621845)
                  ·
                    refine ⟨943755876776355058772387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40266917409124482507621845 943755876776355058772387)
                    ·
                      rfl

theorem cell23_5513874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_5513874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513874 prefixEnd_5513874 := by exact prefixLift 5513874
  have htrace : WordTrace (prefixWord ++ tailWord_5513874) baseStart_5513874 baseEnd_5513874 := by
    simpa [prefixWord, tailWord_5513874, baseEnd_5513874] using wordTrace_append hprefix tailTrace_5513874
  have hstable : (prefixWord ++ tailWord_5513874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513874).length < 2 ^ (prefixWord ++ tailWord_5513874).sum := by decide
  have hdescent : baseEnd_5513874 < baseStart_5513874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513897 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 3]
def baseStart_5513897 : Nat := 118140960795 + 5513897 * 2 ^ 59
def prefixEnd_5513897 : Nat := 4983230072969 + 3 ^ 40 * 5513897 * 2
def baseEnd_5513897 : Nat := 2831279440384118586329555

theorem tailTrace_5513897 : CollatzResearch.WordTrace tailWord_5513897 prefixEnd_5513897 2831279440384118586329555 := by
  unfold tailWord_5513897
  simp only [CollatzResearch.WordTrace]
  refine ⟨201108345305100342480251945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134072230203400228320167963 201108345305100342480251945)
  ·
    refine ⟨150831258978825256860188959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201108345305100342480251945 150831258978825256860188959)
    ·
      refine ⟨226246888468237885290283439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150831258978825256860188959 226246888468237885290283439)
      ·
        refine ⟨339370332702356827935425159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226246888468237885290283439 339370332702356827935425159)
        ·
          refine ⟨509055499053535241903137739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339370332702356827935425159 509055499053535241903137739)
          ·
            refine ⟨763583248580302862854706609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509055499053535241903137739 763583248580302862854706609)
            ·
              refine ⟨572687436435227147141029957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763583248580302862854706609 572687436435227147141029957)
              ·
                refine ⟨107378894331605090088943117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572687436435227147141029957 107378894331605090088943117)
                ·
                  refine ⟨40267085374351908783353669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107378894331605090088943117 40267085374351908783353669)
                  ·
                    refine ⟨7550078507690982896878813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40267085374351908783353669 7550078507690982896878813)
                    ·
                      refine ⟨2831279440384118586329555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550078507690982896878813 2831279440384118586329555)
                      ·
                        rfl

theorem cell23_5513897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_5513897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513897 prefixEnd_5513897 := by exact prefixLift 5513897
  have htrace : WordTrace (prefixWord ++ tailWord_5513897) baseStart_5513897 baseEnd_5513897 := by
    simpa [prefixWord, tailWord_5513897, baseEnd_5513897] using wordTrace_append hprefix tailTrace_5513897
  have hstable : (prefixWord ++ tailWord_5513897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513897).length < 2 ^ (prefixWord ++ tailWord_5513897).sum := by decide
  have hdescent : baseEnd_5513897 < baseStart_5513897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513948 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5513948 : Nat := 118140960795 + 5513948 * 2 ^ 59
def prefixEnd_5513948 : Nat := 4983230072969 + 3 ^ 40 * 5513948 * 2
def baseEnd_5513948 : Nat := 2831305627897497886791821

theorem tailTrace_5513948 : CollatzResearch.WordTrace tailWord_5513948 prefixEnd_5513948 2831305627897497886791821 := by
  unfold tailWord_5513948
  simp only [CollatzResearch.WordTrace]
  refine ⟨100555102713957789095179249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134073470285277052126905665 100555102713957789095179249)
  ·
    refine ⟨75416327035468341821384437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100555102713957789095179249 75416327035468341821384437)
    ·
      refine ⟨7070280659575157045754791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75416327035468341821384437 7070280659575157045754791)
      ·
        refine ⟨10605420989362735568632187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7070280659575157045754791 10605420989362735568632187)
        ·
          refine ⟨15908131484044103352948281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10605420989362735568632187 15908131484044103352948281)
          ·
            refine ⟨11931098613033077514711211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15908131484044103352948281 11931098613033077514711211)
            ·
              refine ⟨17896647919549616272066817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11931098613033077514711211 17896647919549616272066817)
              ·
                refine ⟨13422485939662212204050113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17896647919549616272066817 13422485939662212204050113)
                ·
                  refine ⟨10066864454746659153037585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13422485939662212204050113 10066864454746659153037585)
                  ·
                    refine ⟨7550148341059994364778189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10066864454746659153037585 7550148341059994364778189)
                    ·
                      refine ⟨2831305627897497886791821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550148341059994364778189 2831305627897497886791821)
                      ·
                        rfl

theorem cell23_5513948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5513948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513948 prefixEnd_5513948 := by exact prefixLift 5513948
  have htrace : WordTrace (prefixWord ++ tailWord_5513948) baseStart_5513948 baseEnd_5513948 := by
    simpa [prefixWord, tailWord_5513948, baseEnd_5513948] using wordTrace_append hprefix tailTrace_5513948
  have hstable : (prefixWord ++ tailWord_5513948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513948).length < 2 ^ (prefixWord ++ tailWord_5513948).sum := by decide
  have hdescent : baseEnd_5513948 < baseStart_5513948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513955 : List Nat := [1, 1, 1, 7, 1, 2, 3, 2, 1, 4]
def baseStart_5513955 : Nat := 118140960795 + 5513955 * 2 ^ 59
def prefixEnd_5513955 : Nat := 4983230072969 + 3 ^ 40 * 5513955 * 2
def baseEnd_5513955 : Nat := 943769740754026453134763

theorem tailTrace_5513955 : CollatzResearch.WordTrace tailWord_5513955 prefixEnd_5513955 943769740754026453134763 := by
  unfold tailWord_5513955
  simp only [CollatzResearch.WordTrace]
  refine ⟨201110460738890218385863319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134073640492593478923908879 201110460738890218385863319)
  ·
    refine ⟨301665691108335327578794979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201110460738890218385863319 301665691108335327578794979)
    ·
      refine ⟨452498536662502991368192469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301665691108335327578794979 452498536662502991368192469)
      ·
        refine ⟨10605434453027413860192011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 452498536662502991368192469 10605434453027413860192011)
        ·
          refine ⟨15908151679541120790288017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10605434453027413860192011 15908151679541120790288017)
          ·
            refine ⟨11931113759655840592716013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15908151679541120790288017 11931113759655840592716013)
            ·
              refine ⟨4474167659870940222268505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11931113759655840592716013 4474167659870940222268505)
              ·
                refine ⟨3355625744903205166701379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474167659870940222268505 3355625744903205166701379)
                ·
                  refine ⟨5033438617354807750052069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355625744903205166701379 5033438617354807750052069)
                  ·
                    refine ⟨943769740754026453134763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5033438617354807750052069 943769740754026453134763)
                    ·
                      rfl

theorem cell23_5513955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 4].length) (baseStart_5513955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513955 prefixEnd_5513955 := by exact prefixLift 5513955
  have htrace : WordTrace (prefixWord ++ tailWord_5513955) baseStart_5513955 baseEnd_5513955 := by
    simpa [prefixWord, tailWord_5513955, baseEnd_5513955] using wordTrace_append hprefix tailTrace_5513955
  have hstable : (prefixWord ++ tailWord_5513955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513955).length < 2 ^ (prefixWord ++ tailWord_5513955).sum := by decide
  have hdescent : baseEnd_5513955 < baseStart_5513955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513961 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 3]
def baseStart_5513961 : Nat := 118140960795 + 5513961 * 2 ^ 59
def prefixEnd_5513961 : Nat := 4983230072969 + 3 ^ 40 * 5513961 * 2
def baseEnd_5513961 : Nat := 2831312303146006335929261

theorem tailTrace_5513961 : CollatzResearch.WordTrace tailWord_5513961 prefixEnd_5513961 2831312303146006335929261 := by
  unfold tailWord_5513961
  simp only [CollatzResearch.WordTrace]
  refine ⟨201110679576868481410581737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134073786384578987607054491 201110679576868481410581737)
  ·
    refine ⟨150833009682651361057936303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201110679576868481410581737 150833009682651361057936303)
    ·
      refine ⟨226249514523977041586904455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150833009682651361057936303 226249514523977041586904455)
      ·
        refine ⟨339374271785965562380356683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226249514523977041586904455 339374271785965562380356683)
        ·
          refine ⟨509061407678948343570535025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339374271785965562380356683 509061407678948343570535025)
          ·
            refine ⟨381796055759211257677901269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509061407678948343570535025 381796055759211257677901269)
            ·
              refine ⟨8948345056856513851825811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 381796055759211257677901269 8948345056856513851825811)
              ·
                refine ⟨13422517585284770777738717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8948345056856513851825811 13422517585284770777738717)
                ·
                  refine ⟨5033444094481789041652019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13422517585284770777738717 5033444094481789041652019)
                  ·
                    refine ⟨7550166141722683562478029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5033444094481789041652019 7550166141722683562478029)
                    ·
                      refine ⟨2831312303146006335929261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550166141722683562478029 2831312303146006335929261)
                      ·
                        rfl

theorem cell23_5513961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 3].length) (baseStart_5513961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513961 prefixEnd_5513961 := by exact prefixLift 5513961
  have htrace : WordTrace (prefixWord ++ tailWord_5513961) baseStart_5513961 baseEnd_5513961 := by
    simpa [prefixWord, tailWord_5513961, baseEnd_5513961] using wordTrace_append hprefix tailTrace_5513961
  have hstable : (prefixWord ++ tailWord_5513961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513961).length < 2 ^ (prefixWord ++ tailWord_5513961).sum := by decide
  have hdescent : baseEnd_5513961 < baseStart_5513961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513977 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 5, 6]
def baseStart_5513977 : Nat := 118140960795 + 5513977 * 2 ^ 59
def prefixEnd_5513977 : Nat := 4983230072969 + 3 ^ 40 * 5513977 * 2
def baseEnd_5513977 : Nat := 943773506278826091109729

theorem tailTrace_5513977 : CollatzResearch.WordTrace tailWord_5513977 prefixEnd_5513977 943773506278826091109729 := by
  unfold tailWord_5513977
  simp only [CollatzResearch.WordTrace]
  refine ⟨201111263144810516143164185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134074175429873677428776123 201111263144810516143164185)
  ·
    refine ⟨150833447358607887107373139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201111263144810516143164185 150833447358607887107373139)
    ·
      refine ⟨226250171037911830661059709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150833447358607887107373139 226250171037911830661059709)
      ·
        refine ⟨84843814139216936497897391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226250171037911830661059709 84843814139216936497897391)
        ·
          refine ⟨127265721208825404746846087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84843814139216936497897391 127265721208825404746846087)
          ·
            refine ⟨190898581813238107120269131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127265721208825404746846087 190898581813238107120269131)
            ·
              refine ⟨286347872719857160680403697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190898581813238107120269131 286347872719857160680403697)
              ·
                refine ⟨214760904539892870510302773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286347872719857160680403697 214760904539892870510302773)
                ·
                  refine ⟨20133834800614956610340885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214760904539892870510302773 20133834800614956610340885)
                  ·
                    refine ⟨943773506278826091109729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20133834800614956610340885 943773506278826091109729)
                    ·
                      rfl

theorem cell23_5513977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_5513977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513977 prefixEnd_5513977 := by exact prefixLift 5513977
  have htrace : WordTrace (prefixWord ++ tailWord_5513977) baseStart_5513977 baseEnd_5513977 := by
    simpa [prefixWord, tailWord_5513977, baseEnd_5513977] using wordTrace_append hprefix tailTrace_5513977
  have hstable : (prefixWord ++ tailWord_5513977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513977).length < 2 ^ (prefixWord ++ tailWord_5513977).sum := by decide
  have hdescent : baseEnd_5513977 < baseStart_5513977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513988 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_5513988 : Nat := 118140960795 + 5513988 * 2 ^ 59
def prefixEnd_5513988 : Nat := 4983230072969 + 3 ^ 40 * 5513988 * 2
def baseEnd_5513988 : Nat := 2831326167123677730291637

theorem tailTrace_5513988 : CollatzResearch.WordTrace tailWord_5513988 prefixEnd_5513988 2831326167123677730291637 := by
  unfold tailWord_5513988
  simp only [CollatzResearch.WordTrace]
  refine ⟨100555832173885332510907309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134074442898513776681209745 100555832173885332510907309)
  ·
    refine ⟨37708437065206999691590241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100555832173885332510907309 37708437065206999691590241)
    ·
      refine ⟨28281327798905249768692681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37708437065206999691590241 28281327798905249768692681)
      ·
        refine ⟨21210995849178937326519511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28281327798905249768692681 21210995849178937326519511)
        ·
          refine ⟨31816493773768405989779267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21210995849178937326519511 31816493773768405989779267)
          ·
            refine ⟨47724740660652608984668901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31816493773768405989779267 47724740660652608984668901)
            ·
              refine ⟨8948388873872364184625419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47724740660652608984668901 8948388873872364184625419)
              ·
                refine ⟨13422583310808546276938129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8948388873872364184625419 13422583310808546276938129)
                ·
                  refine ⟨10066937483106409707703597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13422583310808546276938129 10066937483106409707703597)
                  ·
                    refine ⟨3775101556164903640388849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10066937483106409707703597 3775101556164903640388849)
                    ·
                      refine ⟨2831326167123677730291637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775101556164903640388849 2831326167123677730291637)
                      ·
                        rfl

theorem cell23_5513988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_5513988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513988 prefixEnd_5513988 := by exact prefixLift 5513988
  have htrace : WordTrace (prefixWord ++ tailWord_5513988) baseStart_5513988 baseEnd_5513988 := by
    simpa [prefixWord, tailWord_5513988, baseEnd_5513988] using wordTrace_append hprefix tailTrace_5513988
  have hstable : (prefixWord ++ tailWord_5513988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513988).length < 2 ^ (prefixWord ++ tailWord_5513988).sum := by decide
  have hdescent : baseEnd_5513988 < baseStart_5513988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513994 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_5513994 : Nat := 118140960795 + 5513994 * 2 ^ 59
def prefixEnd_5513994 : Nat := 4983230072969 + 3 ^ 40 * 5513994 * 2
def baseEnd_5513994 : Nat := 943776416002534902272203

theorem tailTrace_5513994 : CollatzResearch.WordTrace tailWord_5513994 prefixEnd_5513994 943776416002534902272203 := by
  unfold tailWord_5513994
  simp only [CollatzResearch.WordTrace]
  refine ⟨50277970796437232011633259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134074588790499285364355357 50277970796437232011633259)
  ·
    refine ⟨75416956194655848017449889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50277970796437232011633259 75416956194655848017449889)
    ·
      refine ⟨56562717145991886013087417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75416956194655848017449889 56562717145991886013087417)
      ·
        refine ⟨42422037859493914509815563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56562717145991886013087417 42422037859493914509815563)
        ·
          refine ⟨63633056789240871764723345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42422037859493914509815563 63633056789240871764723345)
          ·
            refine ⟨47724792591930653823542509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63633056789240871764723345 47724792591930653823542509)
            ·
              refine ⟨17896797221973995183828441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47724792591930653823542509 17896797221973995183828441)
              ·
                refine ⟨13422597916480496387871331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17896797221973995183828441 13422597916480496387871331)
                ·
                  refine ⟨20133896874720744581806997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13422597916480496387871331 20133896874720744581806997)
                  ·
                    refine ⟨943776416002534902272203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20133896874720744581806997 943776416002534902272203)
                    ·
                      rfl

theorem cell23_5513994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_5513994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5513994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5513994 prefixEnd_5513994 := by exact prefixLift 5513994
  have htrace : WordTrace (prefixWord ++ tailWord_5513994) baseStart_5513994 baseEnd_5513994 := by
    simpa [prefixWord, tailWord_5513994, baseEnd_5513994] using wordTrace_append hprefix tailTrace_5513994
  have hstable : (prefixWord ++ tailWord_5513994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513994).length < 2 ^ (prefixWord ++ tailWord_5513994).sum := by decide
  have hdescent : baseEnd_5513994 < baseStart_5513994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514007 : List Nat := [1, 1, 3, 4, 14]
def baseStart_5514007 : Nat := 118140960795 + 5514007 * 2 ^ 59
def prefixEnd_5514007 : Nat := 4983230072969 + 3 ^ 40 * 5514007 * 2
def baseEnd_5514007 : Nat := 3883862720515930255081

theorem tailTrace_5514007 : CollatzResearch.WordTrace tailWord_5514007 prefixEnd_5514007 3883862720515930255081 := by
  unfold tailWord_5514007
  simp only [CollatzResearch.WordTrace]
  refine ⟨201112357334701831266756275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134074904889801220844504183 201112357334701831266756275)
  ·
    refine ⟨301668536002052746900134413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201112357334701831266756275 301668536002052746900134413)
    ·
      refine ⟨113125701000769780087550405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301668536002052746900134413 113125701000769780087550405)
      ·
        refine ⟨21211068937644333766415701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113125701000769780087550405 21211068937644333766415701)
        ·
          refine ⟨3883862720515930255081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 21211068937644333766415701 3883862720515930255081)
          ·
            rfl

theorem cell23_5514007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 14].length) (baseStart_5514007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514007 prefixEnd_5514007 := by exact prefixLift 5514007
  have htrace : WordTrace (prefixWord ++ tailWord_5514007) baseStart_5514007 baseEnd_5514007 := by
    simpa [prefixWord, tailWord_5514007, baseEnd_5514007] using wordTrace_append hprefix tailTrace_5514007
  have hstable : (prefixWord ++ tailWord_5514007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514007).length < 2 ^ (prefixWord ++ tailWord_5514007).sum := by decide
  have hdescent : baseEnd_5514007 < baseStart_5514007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514012 : List Nat := [2, 2, 3, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_5514012 : Nat := 118140960795 + 5514012 * 2 ^ 59
def prefixEnd_5514012 : Nat := 4983230072969 + 3 ^ 40 * 5514012 * 2
def baseEnd_5514012 : Nat := 2831338490659385636391527

theorem tailTrace_5514012 : CollatzResearch.WordTrace tailWord_5514012 prefixEnd_5514012 2831338490659385636391527 := by
  unfold tailWord_5514012
  simp only [CollatzResearch.WordTrace]
  refine ⟨100556269849841858560344145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134075026466455811413792193 100556269849841858560344145)
  ·
    refine ⟨75417202387381393920258109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100556269849841858560344145 75417202387381393920258109)
    ·
      refine ⟨28281450895268022720096791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75417202387381393920258109 28281450895268022720096791)
      ·
        refine ⟨42422176342902034080145187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28281450895268022720096791 42422176342902034080145187)
        ·
          refine ⟨63633264514353051120217781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42422176342902034080145187 63633264514353051120217781)
          ·
            refine ⟨5965618548220598542520417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63633264514353051120217781 5965618548220598542520417)
            ·
              refine ⟨4474213911165448906890313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5965618548220598542520417 4474213911165448906890313)
              ·
                refine ⟨3355660433374086680167735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474213911165448906890313 3355660433374086680167735)
                ·
                  refine ⟨5033490650061130020251603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355660433374086680167735 5033490650061130020251603)
                  ·
                    refine ⟨7550235975091695030377405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5033490650061130020251603 7550235975091695030377405)
                    ·
                      refine ⟨2831338490659385636391527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550235975091695030377405 2831338490659385636391527)
                      ·
                        rfl

theorem cell23_5514012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_5514012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514012 prefixEnd_5514012 := by exact prefixLift 5514012
  have htrace : WordTrace (prefixWord ++ tailWord_5514012) baseStart_5514012 baseEnd_5514012 := by
    simpa [prefixWord, tailWord_5514012, baseEnd_5514012] using wordTrace_append hprefix tailTrace_5514012
  have hstable : (prefixWord ++ tailWord_5514012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514012).length < 2 ^ (prefixWord ++ tailWord_5514012).sum := by decide
  have hdescent : baseEnd_5514012 < baseStart_5514012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514027 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 6]
def baseStart_5514027 : Nat := 118140960795 + 5514027 * 2 ^ 59
def prefixEnd_5514027 : Nat := 4983230072969 + 3 ^ 40 * 5514027 * 2
def baseEnd_5514027 : Nat := 2831346192869203077703957

theorem tailTrace_5514027 : CollatzResearch.WordTrace tailWord_5514027 prefixEnd_5514027 2831346192869203077703957 := by
  unfold tailWord_5514027
  simp only [CollatzResearch.WordTrace]
  refine ⟨201113086794629374682484335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134075391196419583121656223 201113086794629374682484335)
  ·
    refine ⟨301669630191944062023726503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201113086794629374682484335 301669630191944062023726503)
    ·
      refine ⟨452504445287916093035589755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301669630191944062023726503 452504445287916093035589755)
      ·
        refine ⟨678756667931874139553384633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452504445287916093035589755 678756667931874139553384633)
        ·
          refine ⟨509067500948905604665038475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 678756667931874139553384633 509067500948905604665038475)
          ·
            refine ⟨763601251423358406997557713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509067500948905604665038475 763601251423358406997557713)
            ·
              refine ⟨572700938567518805248168285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763601251423358406997557713 572700938567518805248168285)
              ·
                refine ⟨214762851962819551968063107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 572700938567518805248168285 214762851962819551968063107)
                ·
                  refine ⟨322144277944229327952094661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214762851962819551968063107 322144277944229327952094661)
                  ·
                    refine ⟨60402052114542998991017749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322144277944229327952094661 60402052114542998991017749)
                    ·
                      refine ⟨2831346192869203077703957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60402052114542998991017749 2831346192869203077703957)
                      ·
                        rfl

theorem cell23_5514027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_5514027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514027 prefixEnd_5514027 := by exact prefixLift 5514027
  have htrace : WordTrace (prefixWord ++ tailWord_5514027) baseStart_5514027 baseEnd_5514027 := by
    simpa [prefixWord, tailWord_5514027, baseEnd_5514027] using wordTrace_append hprefix tailTrace_5514027
  have hstable : (prefixWord ++ tailWord_5514027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514027).length < 2 ^ (prefixWord ++ tailWord_5514027).sum := by decide
  have hdescent : baseEnd_5514027 < baseStart_5514027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514051 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 3]
def baseStart_5514051 : Nat := 118140960795 + 5514051 * 2 ^ 59
def prefixEnd_5514051 : Nat := 4983230072969 + 3 ^ 40 * 5514051 * 2
def baseEnd_5514051 : Nat := 2831358516404910983803847

theorem tailTrace_5514051 : CollatzResearch.WordTrace tailWord_5514051 prefixEnd_5514051 2831358516404910983803847 := by
  unfold tailWord_5514051
  simp only [CollatzResearch.WordTrace]
  refine ⟨201113962146542426781358007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134075974764361617854238671 201113962146542426781358007)
  ·
    refine ⟨301670943219813640172037011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201113962146542426781358007 301670943219813640172037011)
    ·
      refine ⟨452506414829720460258055517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301670943219813640172037011 452506414829720460258055517)
      ·
        refine ⟨169689905561145172596770819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 452506414829720460258055517 169689905561145172596770819)
        ·
          refine ⟨254534858341717758895156229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169689905561145172596770819 254534858341717758895156229)
          ·
            refine ⟨47725285939072079792841793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254534858341717758895156229 47725285939072079792841793)
            ·
              refine ⟨35793964454304059844631345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47725285939072079792841793 35793964454304059844631345)
              ·
                refine ⟨26845473340728044883473509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35793964454304059844631345 26845473340728044883473509)
                ·
                  refine ⟨5033526251386508415651283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26845473340728044883473509 5033526251386508415651283)
                  ·
                    refine ⟨7550289377079762623476925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5033526251386508415651283 7550289377079762623476925)
                    ·
                      refine ⟨2831358516404910983803847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550289377079762623476925 2831358516404910983803847)
                      ·
                        rfl

theorem cell23_5514051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_5514051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514051 prefixEnd_5514051 := by exact prefixLift 5514051
  have htrace : WordTrace (prefixWord ++ tailWord_5514051) baseStart_5514051 baseEnd_5514051 := by
    simpa [prefixWord, tailWord_5514051, baseEnd_5514051] using wordTrace_append hprefix tailTrace_5514051
  have hstable : (prefixWord ++ tailWord_5514051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514051).length < 2 ^ (prefixWord ++ tailWord_5514051).sum := by decide
  have hdescent : baseEnd_5514051 < baseStart_5514051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514104 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_5514104 : Nat := 118140960795 + 5514104 * 2 ^ 59
def prefixEnd_5514104 : Nat := 4983230072969 + 3 ^ 40 * 5514104 * 2
def baseEnd_5514104 : Nat := 2831385730879599276441103

theorem tailTrace_5514104 : CollatzResearch.WordTrace tailWord_5514104 prefixEnd_5514104 2831385730879599276441103 := by
  unfold tailWord_5514104
  simp only [CollatzResearch.WordTrace]
  refine ⟨100557947607675208416518683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134077263476900277888691577 100557947607675208416518683)
  ·
    refine ⟨150836921411512812624778025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100557947607675208416518683 150836921411512812624778025)
    ·
      refine ⟨113127691058634609468583519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150836921411512812624778025 113127691058634609468583519)
      ·
        refine ⟨169691536587951914202875279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113127691058634609468583519 169691536587951914202875279)
        ·
          refine ⟨254537304881927871304312919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169691536587951914202875279 254537304881927871304312919)
          ·
            refine ⟨381805957322891806956469379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254537304881927871304312919 381805957322891806956469379)
            ·
              refine ⟨572708935984337710434704069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381805957322891806956469379 572708935984337710434704069)
              ·
                refine ⟨107382925497063320706507013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572708935984337710434704069 107382925497063320706507013)
                ·
                  refine ⟨20134298530699372632470065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107382925497063320706507013 20134298530699372632470065)
                  ·
                    refine ⟨15100723898024529474352549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20134298530699372632470065 15100723898024529474352549)
                    ·
                      refine ⟨2831385730879599276441103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15100723898024529474352549 2831385730879599276441103)
                      ·
                        rfl

theorem cell23_5514104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_5514104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514104 prefixEnd_5514104 := by exact prefixLift 5514104
  have htrace : WordTrace (prefixWord ++ tailWord_5514104) baseStart_5514104 baseEnd_5514104 := by
    simpa [prefixWord, tailWord_5514104, baseEnd_5514104] using wordTrace_append hprefix tailTrace_5514104
  have hstable : (prefixWord ++ tailWord_5514104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514104).length < 2 ^ (prefixWord ++ tailWord_5514104).sum := by decide
  have hdescent : baseEnd_5514104 < baseStart_5514104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514141 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_5514141 : Nat := 118140960795 + 5514141 * 2 ^ 59
def prefixEnd_5514141 : Nat := 4983230072969 + 3 ^ 40 * 5514141 * 2
def baseEnd_5514141 : Nat := 2831404729663815631678433

theorem tailTrace_5514141 : CollatzResearch.WordTrace tailWord_5514141 prefixEnd_5514141 2831404729663815631678433 := by
  unfold tailWord_5514141
  simp only [CollatzResearch.WordTrace]
  refine ⟨201117244716216372152134277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134078163144144248101422851 201117244716216372152134277)
  ·
    refine ⟨37709483384290569778525177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201117244716216372152134277 37709483384290569778525177)
    ·
      refine ⟨28282112538217927333893883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37709483384290569778525177 28282112538217927333893883)
      ·
        refine ⟨42423168807326891000840825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28282112538217927333893883 42423168807326891000840825)
        ·
          refine ⟨31817376605495168250630619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42423168807326891000840825 31817376605495168250630619)
          ·
            refine ⟨47726064908242752375945929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31817376605495168250630619 47726064908242752375945929)
            ·
              refine ⟨35794548681182064281959447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47726064908242752375945929 35794548681182064281959447)
              ·
                refine ⟨53691823021773096422939171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35794548681182064281959447 53691823021773096422939171)
                ·
                  refine ⟨80537734532659644634408757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53691823021773096422939171 80537734532659644634408757)
                  ·
                    refine ⟨7550412612436841684475821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80537734532659644634408757 7550412612436841684475821)
                    ·
                      refine ⟨2831404729663815631678433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550412612436841684475821 2831404729663815631678433)
                      ·
                        rfl

theorem cell23_5514141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_5514141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514141 prefixEnd_5514141 := by exact prefixLift 5514141
  have htrace : WordTrace (prefixWord ++ tailWord_5514141) baseStart_5514141 baseEnd_5514141 := by
    simpa [prefixWord, tailWord_5514141, baseEnd_5514141] using wordTrace_append hprefix tailTrace_5514141
  have hstable : (prefixWord ++ tailWord_5514141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514141).length < 2 ^ (prefixWord ++ tailWord_5514141).sum := by decide
  have hdescent : baseEnd_5514141 < baseStart_5514141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514144 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 3, 7]
def baseStart_5514144 : Nat := 118140960795 + 5514144 * 2 ^ 59
def prefixEnd_5514144 : Nat := 4983230072969 + 3 ^ 40 * 5514144 * 2
def baseEnd_5514144 : Nat := 943802090035259706646973

theorem tailTrace_5514144 : CollatzResearch.WordTrace tailWord_5514144 prefixEnd_5514144 943802090035259706646973 := by
  unfold tailWord_5514144
  simp only [CollatzResearch.WordTrace]
  refine ⟨100558677067602751832246743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134078236090137002442995657 100558677067602751832246743)
  ·
    refine ⟨150838015601404127748370115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100558677067602751832246743 150838015601404127748370115)
    ·
      refine ⟨226257023402106191622555173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150838015601404127748370115 226257023402106191622555173)
      ·
        refine ⟨42423191887894910929229095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226257023402106191622555173 42423191887894910929229095)
        ·
          refine ⟨63634787831842366393843643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42423191887894910929229095 63634787831842366393843643)
          ·
            refine ⟨95452181747763549590765465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63634787831842366393843643 95452181747763549590765465)
            ·
              refine ⟨71589136310822662193074099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95452181747763549590765465 71589136310822662193074099)
              ·
                refine ⟨107383704466233993289611149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71589136310822662193074099 107383704466233993289611149)
                ·
                  refine ⟨40268889174837747483604181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107383704466233993289611149 40268889174837747483604181)
                  ·
                    refine ⟨943802090035259706646973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40268889174837747483604181 943802090035259706646973)
                    ·
                      rfl

theorem cell23_5514144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_5514144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514144 prefixEnd_5514144 := by exact prefixLift 5514144
  have htrace : WordTrace (prefixWord ++ tailWord_5514144) baseStart_5514144 baseEnd_5514144 := by
    simpa [prefixWord, tailWord_5514144, baseEnd_5514144] using wordTrace_append hprefix tailTrace_5514144
  have hstable : (prefixWord ++ tailWord_5514144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514144).length < 2 ^ (prefixWord ++ tailWord_5514144).sum := by decide
  have hdescent : baseEnd_5514144 < baseStart_5514144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514215 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_5514215 : Nat := 118140960795 + 5514215 * 2 ^ 59
def prefixEnd_5514215 : Nat := 4983230072969 + 3 ^ 40 * 5514215 * 2
def baseEnd_5514215 : Nat := 2831442727232248342153093

theorem tailTrace_5514215 : CollatzResearch.WordTrace tailWord_5514215 prefixEnd_5514215 2831442727232248342153093 := by
  unfold tailWord_5514215
  simp only [CollatzResearch.WordTrace]
  refine ⟨201119943717948282790328099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134079962478632188526885399 201119943717948282790328099)
  ·
    refine ⟨301679915576922424185492149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201119943717948282790328099 301679915576922424185492149)
    ·
      refine ⟨28282492085336477267389889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301679915576922424185492149 28282492085336477267389889)
      ·
        refine ⟨21211869064002357950542417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28282492085336477267389889 21211869064002357950542417)
        ·
          refine ⟨15908901798001768462906813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21211869064002357950542417 15908901798001768462906813)
          ·
            refine ⟨5965838174250663173590055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15908901798001768462906813 5965838174250663173590055)
            ·
              refine ⟨8948757261375994760385083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5965838174250663173590055 8948757261375994760385083)
              ·
                refine ⟨13423135892063992140577625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8948757261375994760385083 13423135892063992140577625)
                ·
                  refine ⟨10067351919047994105433219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13423135892063992140577625 10067351919047994105433219)
                  ·
                    refine ⟨15101027878571991158149829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10067351919047994105433219 15101027878571991158149829)
                    ·
                      refine ⟨2831442727232248342153093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15101027878571991158149829 2831442727232248342153093)
                      ·
                        rfl

theorem cell23_5514215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_5514215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514215 prefixEnd_5514215 := by exact prefixLift 5514215
  have htrace : WordTrace (prefixWord ++ tailWord_5514215) baseStart_5514215 baseEnd_5514215 := by
    simpa [prefixWord, tailWord_5514215, baseEnd_5514215] using wordTrace_append hprefix tailTrace_5514215
  have hstable : (prefixWord ++ tailWord_5514215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514215).length < 2 ^ (prefixWord ++ tailWord_5514215).sum := by decide
  have hdescent : baseEnd_5514215 < baseStart_5514215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514218 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_5514218 : Nat := 118140960795 + 5514218 * 2 ^ 59
def prefixEnd_5514218 : Nat := 4983230072969 + 3 ^ 40 * 5514218 * 2
def baseEnd_5514218 : Nat := 2831444267674211830415579

theorem tailTrace_5514218 : CollatzResearch.WordTrace tailWord_5514218 prefixEnd_5514218 2831444267674211830415579 := by
  unfold tailWord_5514218
  simp only [CollatzResearch.WordTrace]
  refine ⟨50280013284234353575671827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134080035424624942868458205 50280013284234353575671827)
  ·
    refine ⟨75420019926351530363507741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50280013284234353575671827 75420019926351530363507741)
    ·
      refine ⟨28282507472381823886315403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75420019926351530363507741 28282507472381823886315403)
      ·
        refine ⟨42423761208572735829473105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28282507472381823886315403 42423761208572735829473105)
        ·
          refine ⟨31817820906429551872104829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42423761208572735829473105 31817820906429551872104829)
          ·
            refine ⟨11931682839911081952039311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31817820906429551872104829 11931682839911081952039311)
            ·
              refine ⟨17897524259866622928058967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11931682839911081952039311 17897524259866622928058967)
              ·
                refine ⟨26846286389799934392088451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17897524259866622928058967 26846286389799934392088451)
                ·
                  refine ⟨40269429584699901588132677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26846286389799934392088451 40269429584699901588132677)
                  ·
                    refine ⟨7550518047131231547774877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40269429584699901588132677 7550518047131231547774877)
                    ·
                      refine ⟨2831444267674211830415579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550518047131231547774877 2831444267674211830415579)
                      ·
                        rfl

theorem cell23_5514218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_5514218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514218 prefixEnd_5514218 := by exact prefixLift 5514218
  have htrace : WordTrace (prefixWord ++ tailWord_5514218) baseStart_5514218 baseEnd_5514218 := by
    simpa [prefixWord, tailWord_5514218, baseEnd_5514218] using wordTrace_append hprefix tailTrace_5514218
  have hstable : (prefixWord ++ tailWord_5514218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514218).length < 2 ^ (prefixWord ++ tailWord_5514218).sum := by decide
  have hdescent : baseEnd_5514218 < baseStart_5514218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514225 : List Nat := [1, 2, 2, 2, 4, 1, 1, 5, 1, 4]
def baseStart_5514225 : Nat := 118140960795 + 5514225 * 2 ^ 59
def prefixEnd_5514225 : Nat := 4983230072969 + 3 ^ 40 * 5514225 * 2
def baseEnd_5514225 : Nat := 943815954012931101009349

theorem tailTrace_5514225 : CollatzResearch.WordTrace tailWord_5514225 prefixEnd_5514225 943815954012931101009349 := by
  unfold tailWord_5514225
  simp only [CollatzResearch.WordTrace]
  refine ⟨201120308447912054498192129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134080205631941369665461419 201120308447912054498192129)
  ·
    refine ⟨150840231335934040873644097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201120308447912054498192129 150840231335934040873644097)
    ·
      refine ⟨113130173501950530655233073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150840231335934040873644097 113130173501950530655233073)
      ·
        refine ⟨84847630126462897991424805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113130173501950530655233073 84847630126462897991424805)
        ·
          refine ⟨15908930648711793373392151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84847630126462897991424805 15908930648711793373392151)
          ·
            refine ⟨23863395973067690060088227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15908930648711793373392151 23863395973067690060088227)
            ·
              refine ⟨35795093959601535090132341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23863395973067690060088227 35795093959601535090132341)
              ·
                refine ⟨3355790058712643914699907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35795093959601535090132341 3355790058712643914699907)
                ·
                  refine ⟨5033685088068965872049861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355790058712643914699907 5033685088068965872049861)
                  ·
                    refine ⟨943815954012931101009349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5033685088068965872049861 943815954012931101009349)
                    ·
                      rfl

theorem cell23_5514225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_5514225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514225 prefixEnd_5514225 := by exact prefixLift 5514225
  have htrace : WordTrace (prefixWord ++ tailWord_5514225) baseStart_5514225 baseEnd_5514225 := by
    simpa [prefixWord, tailWord_5514225, baseEnd_5514225] using wordTrace_append hprefix tailTrace_5514225
  have hstable : (prefixWord ++ tailWord_5514225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514225).length < 2 ^ (prefixWord ++ tailWord_5514225).sum := by decide
  have hdescent : baseEnd_5514225 < baseStart_5514225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514241 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_5514241 : Nat := 118140960795 + 5514241 * 2 ^ 59
def prefixEnd_5514241 : Nat := 4983230072969 + 3 ^ 40 * 5514241 * 2
def baseEnd_5514241 : Nat := 2831456077729265240427973

theorem tailTrace_5514241 : CollatzResearch.WordTrace tailWord_5514241 prefixEnd_5514241 2831456077729265240427973 := by
  unfold tailWord_5514241
  simp only [CollatzResearch.WordTrace]
  refine ⟨201120892015854089230774577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134080594677236059487183051 201120892015854089230774577)
  ·
    refine ⟨150840669011890566923080933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201120892015854089230774577 150840669011890566923080933)
    ·
      refine ⟨28282625439729481298077675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150840669011890566923080933 28282625439729481298077675)
      ·
        refine ⟨42423938159594221947116513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28282625439729481298077675 42423938159594221947116513)
        ·
          refine ⟨31817953619695666460337385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42423938159594221947116513 31817953619695666460337385)
          ·
            refine ⟨23863465214771749845253039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31817953619695666460337385 23863465214771749845253039)
            ·
              refine ⟨35795197822157624767879559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23863465214771749845253039 35795197822157624767879559)
              ·
                refine ⟨53692796733236437151819339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35795197822157624767879559 53692796733236437151819339)
                ·
                  refine ⟨80539195099854655727729009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53692796733236437151819339 80539195099854655727729009)
                  ·
                    refine ⟨60404396324890991795796757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80539195099854655727729009 60404396324890991795796757)
                    ·
                      refine ⟨2831456077729265240427973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60404396324890991795796757 2831456077729265240427973)
                      ·
                        rfl

theorem cell23_5514241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_5514241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514241 prefixEnd_5514241 := by exact prefixLift 5514241
  have htrace : WordTrace (prefixWord ++ tailWord_5514241) baseStart_5514241 baseEnd_5514241 := by
    simpa [prefixWord, tailWord_5514241, baseEnd_5514241] using wordTrace_append hprefix tailTrace_5514241
  have hstable : (prefixWord ++ tailWord_5514241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514241).length < 2 ^ (prefixWord ++ tailWord_5514241).sum := by decide
  have hdescent : baseEnd_5514241 < baseStart_5514241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514288 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 4]
def baseStart_5514288 : Nat := 118140960795 + 5514288 * 2 ^ 59
def prefixEnd_5514288 : Nat := 4983230072969 + 3 ^ 40 * 5514288 * 2
def baseEnd_5514288 : Nat := 2831480211320026556540257

theorem tailTrace_5514288 : CollatzResearch.WordTrace tailWord_5514288 prefixEnd_5514288 2831480211320026556540257 := by
  unfold tailWord_5514288
  simp only [CollatzResearch.WordTrace]
  refine ⟨100561303123341908128867759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134081737497789210838490345 100561303123341908128867759)
  ·
    refine ⟨150841954685012862193301639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100561303123341908128867759 150841954685012862193301639)
    ·
      refine ⟨226262932027519293289952459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150841954685012862193301639 226262932027519293289952459)
      ·
        refine ⟨339394398041278939934928689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226262932027519293289952459 339394398041278939934928689)
        ·
          refine ⟨254545798530959204951196517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339394398041278939934928689 254545798530959204951196517)
          ·
            refine ⟨47727337224554850928349347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254545798530959204951196517 47727337224554850928349347)
            ·
              refine ⟨71591005836832276392524021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47727337224554850928349347 71591005836832276392524021)
              ·
                refine ⟨6711656797203025911799127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71591005836832276392524021 6711656797203025911799127)
                ·
                  refine ⟨10067485195804538867698691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6711656797203025911799127 10067485195804538867698691)
                  ·
                    refine ⟨15101227793706808301548037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10067485195804538867698691 15101227793706808301548037)
                    ·
                      refine ⟨2831480211320026556540257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15101227793706808301548037 2831480211320026556540257)
                      ·
                        rfl

theorem cell23_5514288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 4].length) (baseStart_5514288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514288 prefixEnd_5514288 := by exact prefixLift 5514288
  have htrace : WordTrace (prefixWord ++ tailWord_5514288) baseStart_5514288 baseEnd_5514288 := by
    simpa [prefixWord, tailWord_5514288, baseEnd_5514288] using wordTrace_append hprefix tailTrace_5514288
  have hstable : (prefixWord ++ tailWord_5514288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514288).length < 2 ^ (prefixWord ++ tailWord_5514288).sum := by decide
  have hdescent : baseEnd_5514288 < baseStart_5514288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514292 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_5514292 : Nat := 118140960795 + 5514292 * 2 ^ 59
def prefixEnd_5514292 : Nat := 4983230072969 + 3 ^ 40 * 5514292 * 2
def baseEnd_5514292 : Nat := 2831482265242644540890239

theorem tailTrace_5514292 : CollatzResearch.WordTrace tailWord_5514292 prefixEnd_5514292 2831482265242644540890239 := by
  unfold tailWord_5514292
  simp only [CollatzResearch.WordTrace]
  refine ⟨100561376069334662470440565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134081834759112883293920753 100561376069334662470440565)
  ·
    refine ⟨9427629006500124606603803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100561376069334662470440565 9427629006500124606603803)
    ·
      refine ⟨14141443509750186909905705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9427629006500124606603803 14141443509750186909905705)
      ·
        refine ⟨10606082632312640182429279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14141443509750186909905705 10606082632312640182429279)
        ·
          refine ⟨15909123948468960273643919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10606082632312640182429279 15909123948468960273643919)
          ·
            refine ⟨23863685922703440410465879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15909123948468960273643919 23863685922703440410465879)
            ·
              refine ⟨35795528884055160615698819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23863685922703440410465879 35795528884055160615698819)
              ·
                refine ⟨53693293326082740923548229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35795528884055160615698819 53693293326082740923548229)
                ·
                  refine ⟨10067492498640513923165293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53693293326082740923548229 10067492498640513923165293)
                  ·
                    refine ⟨3775309686990192721186985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10067492498640513923165293 3775309686990192721186985)
                    ·
                      refine ⟨2831482265242644540890239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775309686990192721186985 2831482265242644540890239)
                      ·
                        rfl

theorem cell23_5514292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_5514292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514292 prefixEnd_5514292 := by exact prefixLift 5514292
  have htrace : WordTrace (prefixWord ++ tailWord_5514292) baseStart_5514292 baseEnd_5514292 := by
    simpa [prefixWord, tailWord_5514292, baseEnd_5514292] using wordTrace_append hprefix tailTrace_5514292
  have hstable : (prefixWord ++ tailWord_5514292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514292).length < 2 ^ (prefixWord ++ tailWord_5514292).sum := by decide
  have hdescent : baseEnd_5514292 < baseStart_5514292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514298 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_5514298 : Nat := 118140960795 + 5514298 * 2 ^ 59
def prefixEnd_5514298 : Nat := 4983230072969 + 3 ^ 40 * 5514298 * 2
def baseEnd_5514298 : Nat := 943828448708857172471737

theorem tailTrace_5514298 : CollatzResearch.WordTrace tailWord_5514298 prefixEnd_5514298 943828448708857172471737 := by
  unfold tailWord_5514298
  simp only [CollatzResearch.WordTrace]
  refine ⟨50280742744161896991399887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134081980651098391977066365 50280742744161896991399887)
  ·
    refine ⟨75421114116242845487099831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50280742744161896991399887 75421114116242845487099831)
    ·
      refine ⟨113131671174364268230649747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75421114116242845487099831 113131671174364268230649747)
      ·
        refine ⟨169697506761546402345974621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113131671174364268230649747 169697506761546402345974621)
        ·
          refine ⟨63636565035579900879740483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169697506761546402345974621 63636565035579900879740483)
          ·
            refine ⟨95454847553369851319610725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63636565035579900879740483 95454847553369851319610725)
            ·
              refine ⟨17897783916256847122427011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95454847553369851319610725 17897783916256847122427011)
              ·
                refine ⟨26846675874385270683640517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17897783916256847122427011 26846675874385270683640517)
                ·
                  refine ⟨5033751726447238253182597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26846675874385270683640517 5033751726447238253182597)
                  ·
                    refine ⟨943828448708857172471737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5033751726447238253182597 943828448708857172471737)
                    ·
                      rfl

theorem cell23_5514298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_5514298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514298 prefixEnd_5514298 := by exact prefixLift 5514298
  have htrace : WordTrace (prefixWord ++ tailWord_5514298) baseStart_5514298 baseEnd_5514298 := by
    simpa [prefixWord, tailWord_5514298, baseEnd_5514298] using wordTrace_append hprefix tailTrace_5514298
  have hstable : (prefixWord ++ tailWord_5514298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514298).length < 2 ^ (prefixWord ++ tailWord_5514298).sum := by decide
  have hdescent : baseEnd_5514298 < baseStart_5514298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514311 : List Nat := [1, 1, 4, 1, 3, 2, 1, 10]
def baseStart_5514311 : Nat := 118140960795 + 5514311 * 2 ^ 59
def prefixEnd_5514311 : Nat := 4983230072969 + 3 ^ 40 * 5514311 * 2
def baseEnd_5514311 : Nat := 104870074865743702464913

theorem tailTrace_5514311 : CollatzResearch.WordTrace tailWord_5514311 prefixEnd_5514311 104870074865743702464913 := by
  unfold tailWord_5514311
  simp only [CollatzResearch.WordTrace]
  refine ⟨201123445125600491185822787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134082296750400327457215191 201123445125600491185822787)
  ·
    refine ⟨301685167688400736778734181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201123445125600491185822787 301685167688400736778734181)
    ·
      refine ⟨56565968941575138146012659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301685167688400736778734181 56565968941575138146012659)
      ·
        refine ⟨84848953412362707219018989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56565968941575138146012659 84848953412362707219018989)
        ·
          refine ⟨31818357529636015207132121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84848953412362707219018989 31818357529636015207132121)
          ·
            refine ⟨23863768147227011405349091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31818357529636015207132121 23863768147227011405349091)
            ·
              refine ⟨35795652220840517108023637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23863768147227011405349091 35795652220840517108023637)
              ·
                refine ⟨104870074865743702464913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35795652220840517108023637 104870074865743702464913)
                ·
                  rfl

theorem cell23_5514311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 10].length) (baseStart_5514311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514311 prefixEnd_5514311 := by exact prefixLift 5514311
  have htrace : WordTrace (prefixWord ++ tailWord_5514311) baseStart_5514311 baseEnd_5514311 := by
    simpa [prefixWord, tailWord_5514311, baseEnd_5514311] using wordTrace_append hprefix tailTrace_5514311
  have hstable : (prefixWord ++ tailWord_5514311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514311).length < 2 ^ (prefixWord ++ tailWord_5514311).sum := by decide
  have hdescent : baseEnd_5514311 < baseStart_5514311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514318 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_5514318 : Nat := 118140960795 + 5514318 * 2 ^ 59
def prefixEnd_5514318 : Nat := 4983230072969 + 3 ^ 40 * 5514318 * 2
def baseEnd_5514318 : Nat := 2831495615739661439165119

theorem tailTrace_5514318 : CollatzResearch.WordTrace tailWord_5514318 prefixEnd_5514318 2831495615739661439165119 := by
  unfold tailWord_5514318
  simp only [CollatzResearch.WordTrace]
  refine ⟨25140462554571891422665951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134082466957716754254218405 25140462554571891422665951)
  ·
    refine ⟨37710693831857837133998927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25140462554571891422665951 37710693831857837133998927)
    ·
      refine ⟨56566040747786755700998391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37710693831857837133998927 56566040747786755700998391)
      ·
        refine ⟨84849061121680133551497587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56566040747786755700998391 84849061121680133551497587)
        ·
          refine ⟨127273591682520200327246381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84849061121680133551497587 127273591682520200327246381)
          ·
            refine ⟨47727596880945075122717393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127273591682520200327246381 47727596880945075122717393)
            ·
              refine ⟨35795697660708806342038045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47727596880945075122717393 35795697660708806342038045)
              ·
                refine ⟨13423386622765802378264267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35795697660708806342038045 13423386622765802378264267)
                ·
                  refine ⟨20135079934148703567396401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13423386622765802378264267 20135079934148703567396401)
                  ·
                    refine ⟨15101309950611527675547301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20135079934148703567396401 15101309950611527675547301)
                    ·
                      refine ⟨2831495615739661439165119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15101309950611527675547301 2831495615739661439165119)
                      ·
                        rfl

theorem cell23_5514318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_5514318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514318 prefixEnd_5514318 := by exact prefixLift 5514318
  have htrace : WordTrace (prefixWord ++ tailWord_5514318) baseStart_5514318 baseEnd_5514318 := by
    simpa [prefixWord, tailWord_5514318, baseEnd_5514318] using wordTrace_append hprefix tailTrace_5514318
  have hstable : (prefixWord ++ tailWord_5514318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514318).length < 2 ^ (prefixWord ++ tailWord_5514318).sum := by decide
  have hdescent : baseEnd_5514318 < baseStart_5514318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514322 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_5514322 : Nat := 118140960795 + 5514322 * 2 ^ 59
def prefixEnd_5514322 : Nat := 4983230072969 + 3 ^ 40 * 5514322 * 2
def baseEnd_5514322 : Nat := 2831497669662279423515101

theorem tailTrace_5514322 : CollatzResearch.WordTrace tailWord_5514322 prefixEnd_5514322 2831497669662279423515101 := by
  unfold tailWord_5514322
  simp only [CollatzResearch.WordTrace]
  refine ⟨50280961582140160016118305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134082564219040426709648813 50280961582140160016118305)
  ·
    refine ⟨37710721186605120012088729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50280961582140160016118305 37710721186605120012088729)
    ·
      refine ⟨28283040889953840009066547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37710721186605120012088729 28283040889953840009066547)
      ·
        refine ⟨42424561334930760013599821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28283040889953840009066547 42424561334930760013599821)
        ·
          refine ⟨15909210500599035005099933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42424561334930760013599821 15909210500599035005099933)
          ·
            refine ⟨5965953937724638126912475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15909210500599035005099933 5965953937724638126912475)
            ·
              refine ⟨8948930906586957190368713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5965953937724638126912475 8948930906586957190368713)
              ·
                refine ⟨6711698179940217892776535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8948930906586957190368713 6711698179940217892776535)
                ·
                  refine ⟨10067547269910326839164803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6711698179940217892776535 10067547269910326839164803)
                  ·
                    refine ⟨15101320904865490258747205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10067547269910326839164803 15101320904865490258747205)
                    ·
                      refine ⟨2831497669662279423515101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15101320904865490258747205 2831497669662279423515101)
                      ·
                        rfl

theorem cell23_5514322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_5514322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514322 prefixEnd_5514322 := by exact prefixLift 5514322
  have htrace : WordTrace (prefixWord ++ tailWord_5514322) baseStart_5514322 baseEnd_5514322 := by
    simpa [prefixWord, tailWord_5514322, baseEnd_5514322] using wordTrace_append hprefix tailTrace_5514322
  have hstable : (prefixWord ++ tailWord_5514322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514322).length < 2 ^ (prefixWord ++ tailWord_5514322).sum := by decide
  have hdescent : baseEnd_5514322 < baseStart_5514322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514326 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5514326 : Nat := 118140960795 + 5514326 * 2 ^ 59
def prefixEnd_5514326 : Nat := 4983230072969 + 3 ^ 40 * 5514326 * 2
def baseEnd_5514326 : Nat := 2831499723584897407865083

theorem tailTrace_5514326 : CollatzResearch.WordTrace tailWord_5514326 prefixEnd_5514326 2831499723584897407865083 := by
  unfold tailWord_5514326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570249513784134296726177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134082661480364099165079221 12570249513784134296726177)
  ·
    refine ⟨9427687135338100722544633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12570249513784134296726177 9427687135338100722544633)
    ·
      refine ⟨7070765351503575541908475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9427687135338100722544633 7070765351503575541908475)
      ·
        refine ⟨10606148027255363312862713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7070765351503575541908475 10606148027255363312862713)
        ·
          refine ⟨7954611020441522484647035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10606148027255363312862713 7954611020441522484647035)
          ·
            refine ⟨11931916530662283726970553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7954611020441522484647035 11931916530662283726970553)
            ·
              refine ⟨8948937397996712795227915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11931916530662283726970553 8948937397996712795227915)
              ·
                refine ⟨13423406096995069192841873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8948937397996712795227915 13423406096995069192841873)
                ·
                  refine ⟨10067554572746301894631405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13423406096995069192841873 10067554572746301894631405)
                  ·
                    refine ⟨3775332964779863210486777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10067554572746301894631405 3775332964779863210486777)
                    ·
                      refine ⟨2831499723584897407865083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775332964779863210486777 2831499723584897407865083)
                      ·
                        rfl

theorem cell23_5514326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5514326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514326 prefixEnd_5514326 := by exact prefixLift 5514326
  have htrace : WordTrace (prefixWord ++ tailWord_5514326) baseStart_5514326 baseEnd_5514326 := by
    simpa [prefixWord, tailWord_5514326, baseEnd_5514326] using wordTrace_append hprefix tailTrace_5514326
  have hstable : (prefixWord ++ tailWord_5514326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514326).length < 2 ^ (prefixWord ++ tailWord_5514326).sum := by decide
  have hdescent : baseEnd_5514326 < baseStart_5514326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514358 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_5514358 : Nat := 118140960795 + 5514358 * 2 ^ 59
def prefixEnd_5514358 : Nat := 4983230072969 + 3 ^ 40 * 5514358 * 2
def baseEnd_5514358 : Nat := 943838718321947094221645

theorem tailTrace_5514358 : CollatzResearch.WordTrace tailWord_5514358 prefixEnd_5514358 943838718321947094221645 := by
  unfold tailWord_5514358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570322459776888638298983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134083439570953478808522485 12570322459776888638298983)
  ·
    refine ⟨18855483689665332957448475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12570322459776888638298983 18855483689665332957448475)
    ·
      refine ⟨28283225534497999436172713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18855483689665332957448475 28283225534497999436172713)
      ·
        refine ⟨21212419150873499577129535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28283225534497999436172713 21212419150873499577129535)
        ·
          refine ⟨31818628726310249365694303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21212419150873499577129535 31818628726310249365694303)
          ·
            refine ⟨47727943089465374048541455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31818628726310249365694303 47727943089465374048541455)
            ·
              refine ⟨71591914634198061072812183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47727943089465374048541455 71591914634198061072812183)
              ·
                refine ⟨107387871951297091609218275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71591914634198061072812183 107387871951297091609218275)
                ·
                  refine ⟨161081807926945637413827413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107387871951297091609218275 161081807926945637413827413)
                  ·
                    refine ⟨943838718321947094221645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 161081807926945637413827413 943838718321947094221645)
                    ·
                      rfl

theorem cell23_5514358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_5514358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514358 prefixEnd_5514358 := by exact prefixLift 5514358
  have htrace : WordTrace (prefixWord ++ tailWord_5514358) baseStart_5514358 baseEnd_5514358 := by
    simpa [prefixWord, tailWord_5514358, baseEnd_5514358] using wordTrace_append hprefix tailTrace_5514358
  have hstable : (prefixWord ++ tailWord_5514358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514358).length < 2 ^ (prefixWord ++ tailWord_5514358).sum := by decide
  have hdescent : baseEnd_5514358 < baseStart_5514358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514365 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_5514365 : Nat := 118140960795 + 5514365 * 2 ^ 59
def prefixEnd_5514365 : Nat := 4983230072969 + 3 ^ 40 * 5514365 * 2
def baseEnd_5514365 : Nat := 2831519749330422755277403

theorem tailTrace_5514365 : CollatzResearch.WordTrace tailWord_5514365 prefixEnd_5514365 2831519749330422755277403 := by
  unfold tailWord_5514365
  simp only [CollatzResearch.WordTrace]
  refine ⟨201125414667404858408288549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134083609778269905605525699 201125414667404858408288549)
  ·
    refine ⟨37711015250138410951554103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201125414667404858408288549 37711015250138410951554103)
    ·
      refine ⟨56566522875207616427331155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37711015250138410951554103 56566522875207616427331155)
      ·
        refine ⟨84849784312811424640996733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56566522875207616427331155 84849784312811424640996733)
        ·
          refine ⟨31818669117304284240373775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84849784312811424640996733 31818669117304284240373775)
          ·
            refine ⟨47728003675956426360560663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31818669117304284240373775 47728003675956426360560663)
            ·
              refine ⟨71592005513934639540840995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47728003675956426360560663 71592005513934639540840995)
              ·
                refine ⟨107388008270901959311261493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71592005513934639540840995 107388008270901959311261493)
                ·
                  refine ⟨10067625775397058685430765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107388008270901959311261493 10067625775397058685430765)
                  ·
                    refine ⟨3775359665773897007036537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10067625775397058685430765 3775359665773897007036537)
                    ·
                      refine ⟨2831519749330422755277403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775359665773897007036537 2831519749330422755277403)
                      ·
                        rfl

theorem cell23_5514365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_5514365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514365 prefixEnd_5514365 := by exact prefixLift 5514365
  have htrace : WordTrace (prefixWord ++ tailWord_5514365) baseStart_5514365 baseEnd_5514365 := by
    simpa [prefixWord, tailWord_5514365, baseEnd_5514365] using wordTrace_append hprefix tailTrace_5514365
  have hstable : (prefixWord ++ tailWord_5514365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514365).length < 2 ^ (prefixWord ++ tailWord_5514365).sum := by decide
  have hdescent : baseEnd_5514365 < baseStart_5514365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514372 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_5514372 : Nat := 118140960795 + 5514372 * 2 ^ 59
def prefixEnd_5514372 : Nat := 4983230072969 + 3 ^ 40 * 5514372 * 2
def baseEnd_5514372 : Nat := 2831523343695004227889871

theorem tailTrace_5514372 : CollatzResearch.WordTrace tailWord_5514372 prefixEnd_5514372 2831523343695004227889871 := by
  unfold tailWord_5514372
  simp only [CollatzResearch.WordTrace]
  refine ⟨100562834989189749301896685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134083779985586332402528913 100562834989189749301896685)
  ·
    refine ⟨37711063120946155988211257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100562834989189749301896685 37711063120946155988211257)
    ·
      refine ⟨28283297340709616991158443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37711063120946155988211257 28283297340709616991158443)
      ·
        refine ⟨42424946011064425486737665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28283297340709616991158443 42424946011064425486737665)
        ·
          refine ⟨31818709508298319115053249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42424946011064425486737665 31818709508298319115053249)
          ·
            refine ⟨23864032131223739336289937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31818709508298319115053249 23864032131223739336289937)
            ·
              refine ⟨17898024098417804502217453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23864032131223739336289937 17898024098417804502217453)
              ·
                refine ⟨6711759036906676688331545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17898024098417804502217453 6711759036906676688331545)
                ·
                  refine ⟨5033819277680007516248659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6711759036906676688331545 5033819277680007516248659)
                  ·
                    refine ⟨7550728916520011274372989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5033819277680007516248659 7550728916520011274372989)
                    ·
                      refine ⟨2831523343695004227889871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550728916520011274372989 2831523343695004227889871)
                      ·
                        rfl

theorem cell23_5514372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_5514372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514372 prefixEnd_5514372 := by exact prefixLift 5514372
  have htrace : WordTrace (prefixWord ++ tailWord_5514372) baseStart_5514372 baseEnd_5514372 := by
    simpa [prefixWord, tailWord_5514372, baseEnd_5514372] using wordTrace_append hprefix tailTrace_5514372
  have hstable : (prefixWord ++ tailWord_5514372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514372).length < 2 ^ (prefixWord ++ tailWord_5514372).sum := by decide
  have hdescent : baseEnd_5514372 < baseStart_5514372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514378 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_5514378 : Nat := 118140960795 + 5514378 * 2 ^ 59
def prefixEnd_5514378 : Nat := 4983230072969 + 3 ^ 40 * 5514378 * 2
def baseEnd_5514378 : Nat := 2831526424578931204414843

theorem tailTrace_5514378 : CollatzResearch.WordTrace tailWord_5514378 prefixEnd_5514378 2831526424578931204414843 := by
  unfold tailWord_5514378
  simp only [CollatzResearch.WordTrace]
  refine ⟨50281472204089440407127947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134083925877571841085674525 50281472204089440407127947)
  ·
    refine ⟨75422208306134160610691921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50281472204089440407127947 75422208306134160610691921)
    ·
      refine ⟨56566656229600620458018941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75422208306134160610691921 56566656229600620458018941)
      ·
        refine ⟨21212496086100232671757103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56566656229600620458018941 21212496086100232671757103)
        ·
          refine ⟨31818744129150349007635655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21212496086100232671757103 31818744129150349007635655)
          ·
            refine ⟨47728116193725523511453483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31818744129150349007635655 47728116193725523511453483)
            ·
              refine ⟨71592174290588285267180225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47728116193725523511453483 71592174290588285267180225)
              ·
                refine ⟨53694130717941213950385169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71592174290588285267180225 53694130717941213950385169)
                ·
                  refine ⟨40270598038455910462788877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53694130717941213950385169 40270598038455910462788877)
                  ·
                    refine ⟨15101474264420966423545829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40270598038455910462788877 15101474264420966423545829)
                    ·
                      refine ⟨2831526424578931204414843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15101474264420966423545829 2831526424578931204414843)
                      ·
                        rfl

theorem cell23_5514378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_5514378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514378 prefixEnd_5514378 := by exact prefixLift 5514378
  have htrace : WordTrace (prefixWord ++ tailWord_5514378) baseStart_5514378 baseEnd_5514378 := by
    simpa [prefixWord, tailWord_5514378, baseEnd_5514378] using wordTrace_append hprefix tailTrace_5514378
  have hstable : (prefixWord ++ tailWord_5514378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514378).length < 2 ^ (prefixWord ++ tailWord_5514378).sum := by decide
  have hdescent : baseEnd_5514378 < baseStart_5514378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514382 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_5514382 : Nat := 118140960795 + 5514382 * 2 ^ 59
def prefixEnd_5514382 : Nat := 4983230072969 + 3 ^ 40 * 5514382 * 2
def baseEnd_5514382 : Nat := 2831528478501549188764825

theorem tailTrace_5514382 : CollatzResearch.WordTrace tailWord_5514382 prefixEnd_5514382 2831528478501549188764825 := by
  unfold tailWord_5514382
  simp only [CollatzResearch.WordTrace]
  refine ⟨25140754338542908788957175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134084023138895513541104933 25140754338542908788957175)
  ·
    refine ⟨37711131507814363183435763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25140754338542908788957175 37711131507814363183435763)
    ·
      refine ⟨56566697261721544775153645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37711131507814363183435763 56566697261721544775153645)
      ·
        refine ⟨21212511473145579290682617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56566697261721544775153645 21212511473145579290682617)
        ·
          refine ⟨15909383604859184468011963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21212511473145579290682617 15909383604859184468011963)
          ·
            refine ⟨23864075407288776702017945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15909383604859184468011963 23864075407288776702017945)
            ·
              refine ⟨17898056555466582526513459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23864075407288776702017945 17898056555466582526513459)
              ·
                refine ⟨26847084833199873789770189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17898056555466582526513459 26847084833199873789770189)
                ·
                  refine ⟨10067656812449952671163821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26847084833199873789770189 10067656812449952671163821)
                  ·
                    refine ⟨3775371304668732251686433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10067656812449952671163821 3775371304668732251686433)
                    ·
                      refine ⟨2831528478501549188764825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775371304668732251686433 2831528478501549188764825)
                      ·
                        rfl

theorem cell23_5514382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_5514382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514382 prefixEnd_5514382 := by exact prefixLift 5514382
  have htrace : WordTrace (prefixWord ++ tailWord_5514382) baseStart_5514382 baseEnd_5514382 := by
    simpa [prefixWord, tailWord_5514382, baseEnd_5514382] using wordTrace_append hprefix tailTrace_5514382
  have hstable : (prefixWord ++ tailWord_5514382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514382).length < 2 ^ (prefixWord ++ tailWord_5514382).sum := by decide
  have hdescent : baseEnd_5514382 < baseStart_5514382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514399 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5514399 : Nat := 118140960795 + 5514399 * 2 ^ 59
def prefixEnd_5514399 : Nat := 4983230072969 + 3 ^ 40 * 5514399 * 2
def baseEnd_5514399 : Nat := 2831537207672675622252247

theorem tailTrace_5514399 : CollatzResearch.WordTrace tailWord_5514399 prefixEnd_5514399 2831537207672675622252247 := by
  unfold tailWord_5514399
  simp only [CollatzResearch.WordTrace]
  refine ⟨201126654749281682215026251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134084436499521121476684167 201126654749281682215026251)
  ·
    refine ⟨301689982123922523322539377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201126654749281682215026251 301689982123922523322539377)
    ·
      refine ⟨226267486592941892491904533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301689982123922523322539377 226267486592941892491904533)
      ·
        refine ⟨10606288434044151210558025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 226267486592941892491904533 10606288434044151210558025)
        ·
          refine ⟨7954716325533113407918519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10606288434044151210558025 7954716325533113407918519)
          ·
            refine ⟨11932074488299670111877779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7954716325533113407918519 11932074488299670111877779)
            ·
              refine ⟨17898111732449505167816669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11932074488299670111877779 17898111732449505167816669)
              ·
                refine ⟨6711791899668564437931251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17898111732449505167816669 6711791899668564437931251)
                ·
                  refine ⟨10067687849502846656896877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6711791899668564437931251 10067687849502846656896877)
                  ·
                    refine ⟨3775382943563567496336329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10067687849502846656896877 3775382943563567496336329)
                    ·
                      refine ⟨2831537207672675622252247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775382943563567496336329 2831537207672675622252247)
                      ·
                        rfl

theorem cell23_5514399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5514399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514399 prefixEnd_5514399 := by exact prefixLift 5514399
  have htrace : WordTrace (prefixWord ++ tailWord_5514399) baseStart_5514399 baseEnd_5514399 := by
    simpa [prefixWord, tailWord_5514399, baseEnd_5514399] using wordTrace_append hprefix tailTrace_5514399
  have hstable : (prefixWord ++ tailWord_5514399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514399).length < 2 ^ (prefixWord ++ tailWord_5514399).sum := by decide
  have hdescent : baseEnd_5514399 < baseStart_5514399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514412 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 2, 2, 2]
def baseStart_5514412 : Nat := 118140960795 + 5514412 * 2 ^ 59
def prefixEnd_5514412 : Nat := 4983230072969 + 3 ^ 40 * 5514412 * 2
def baseEnd_5514412 : Nat := 2831543882921184071389687

theorem tailTrace_5514412 : CollatzResearch.WordTrace tailWord_5514412 prefixEnd_5514412 2831543882921184071389687 := by
  unfold tailWord_5514412
  simp only [CollatzResearch.WordTrace]
  refine ⟨100563564449117292717624745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134084752598823056956832993 100563564449117292717624745)
  ·
    refine ⟨75422673336837969538218559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100563564449117292717624745 75422673336837969538218559)
    ·
      refine ⟨113134010005256954307327839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75422673336837969538218559 113134010005256954307327839)
      ·
        refine ⟨169701015007885431460991759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113134010005256954307327839 169701015007885431460991759)
        ·
          refine ⟨254551522511828147191487639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169701015007885431460991759 254551522511828147191487639)
          ·
            refine ⟨381827283767742220787231459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254551522511828147191487639 381827283767742220787231459)
            ·
              refine ⟨572740925651613331180847189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381827283767742220787231459 572740925651613331180847189)
              ·
                refine ⟨6711807722479843724775553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 572740925651613331180847189 6711807722479843724775553)
                ·
                  refine ⟨5033855791859882793581665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6711807722479843724775553 5033855791859882793581665)
                  ·
                    refine ⟨3775391843894912095186249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5033855791859882793581665 3775391843894912095186249)
                    ·
                      refine ⟨2831543882921184071389687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775391843894912095186249 2831543882921184071389687)
                      ·
                        rfl

theorem cell23_5514412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_5514412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514412 prefixEnd_5514412 := by exact prefixLift 5514412
  have htrace : WordTrace (prefixWord ++ tailWord_5514412) baseStart_5514412 baseEnd_5514412 := by
    simpa [prefixWord, tailWord_5514412, baseEnd_5514412] using wordTrace_append hprefix tailTrace_5514412
  have hstable : (prefixWord ++ tailWord_5514412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514412).length < 2 ^ (prefixWord ++ tailWord_5514412).sum := by decide
  have hdescent : baseEnd_5514412 < baseStart_5514412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514418 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 7]
def baseStart_5514418 : Nat := 118140960795 + 5514418 * 2 ^ 59
def prefixEnd_5514418 : Nat := 4983230072969 + 3 ^ 40 * 5514418 * 2
def baseEnd_5514418 : Nat := 314616329311679005323851

theorem tailTrace_5514418 : CollatzResearch.WordTrace tailWord_5514418 prefixEnd_5514418 314616329311679005323851 := by
  unfold tailWord_5514418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50281836934053212114991977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134084898490808565639978605 50281836934053212114991977)
  ·
    refine ⟨37711377700539909086243983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50281836934053212114991977 37711377700539909086243983)
    ·
      refine ⟨56567066550809863629365975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37711377700539909086243983 56567066550809863629365975)
      ·
        refine ⟨84850599826214795444048963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56567066550809863629365975 84850599826214795444048963)
        ·
          refine ⟨127275899739322193166073445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84850599826214795444048963 127275899739322193166073445)
          ·
            refine ⟨23864231201122911218638771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127275899739322193166073445 23864231201122911218638771)
            ·
              refine ⟨35796346801684366827958157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23864231201122911218638771 35796346801684366827958157)
              ·
                refine ⟨13423630050631637560484309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35796346801684366827958157 13423630050631637560484309)
                ·
                  refine ⟨314616329311679005323851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13423630050631637560484309 314616329311679005323851)
                  ·
                    rfl

theorem cell23_5514418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_5514418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514418 prefixEnd_5514418 := by exact prefixLift 5514418
  have htrace : WordTrace (prefixWord ++ tailWord_5514418) baseStart_5514418 baseEnd_5514418 := by
    simpa [prefixWord, tailWord_5514418, baseEnd_5514418] using wordTrace_append hprefix tailTrace_5514418
  have hstable : (prefixWord ++ tailWord_5514418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514418).length < 2 ^ (prefixWord ++ tailWord_5514418).sum := by decide
  have hdescent : baseEnd_5514418 < baseStart_5514418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514458 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_5514458 : Nat := 118140960795 + 5514458 * 2 ^ 59
def prefixEnd_5514458 : Nat := 4983230072969 + 3 ^ 40 * 5514458 * 2
def baseEnd_5514458 : Nat := 2831567503031290891414475

theorem tailTrace_5514458 : CollatzResearch.WordTrace tailWord_5514458 prefixEnd_5514458 2831567503031290891414475 := by
  unfold tailWord_5514458
  simp only [CollatzResearch.WordTrace]
  refine ⟨50282201664016983822856007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134085871104045290194282685 50282201664016983822856007)
  ·
    refine ⟨75423302496025475734284011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50282201664016983822856007 75423302496025475734284011)
    ·
      refine ⟨113134953744038213601426017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75423302496025475734284011 113134953744038213601426017)
      ·
        refine ⟨84851215308028660201069513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113134953744038213601426017 84851215308028660201069513)
        ·
          refine ⟨63638411481021495150802135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84851215308028660201069513 63638411481021495150802135)
          ·
            refine ⟨95457617221532242726203203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63638411481021495150802135 95457617221532242726203203)
            ·
              refine ⟨143186425832298364089304805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95457617221532242726203203 143186425832298364089304805)
              ·
                refine ⟨26847454843555943266744651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143186425832298364089304805 26847454843555943266744651)
                ·
                  refine ⟨40271182265333914900116977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26847454843555943266744651 40271182265333914900116977)
                  ·
                    refine ⟨30203386699000436175087733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40271182265333914900116977 30203386699000436175087733)
                    ·
                      refine ⟨2831567503031290891414475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30203386699000436175087733 2831567503031290891414475)
                      ·
                        rfl

theorem cell23_5514458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_5514458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514458 prefixEnd_5514458 := by exact prefixLift 5514458
  have htrace : WordTrace (prefixWord ++ tailWord_5514458) baseStart_5514458 baseEnd_5514458 := by
    simpa [prefixWord, tailWord_5514458, baseEnd_5514458] using wordTrace_append hprefix tailTrace_5514458
  have hstable : (prefixWord ++ tailWord_5514458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514458).length < 2 ^ (prefixWord ++ tailWord_5514458).sum := by decide
  have hdescent : baseEnd_5514458 < baseStart_5514458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514465 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 2, 5]
def baseStart_5514465 : Nat := 118140960795 + 5514465 * 2 ^ 59
def prefixEnd_5514465 : Nat := 4983230072969 + 3 ^ 40 * 5514465 * 2
def baseEnd_5514465 : Nat := 943857032465290788008981

theorem tailTrace_5514465 : CollatzResearch.WordTrace tailWord_5514465 prefixEnd_5514465 943857032465290788008981 := by
  unfold tailWord_5514465
  simp only [CollatzResearch.WordTrace]
  refine ⟨201129061967042575486928849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134086041311361716991285899 201129061967042575486928849)
  ·
    refine ⟨150846796475281931615196637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201129061967042575486928849 150846796475281931615196637)
    ·
      refine ⟨56567548678230724355698739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150846796475281931615196637 56567548678230724355698739)
      ·
        refine ⟨84851323017346086533548109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56567548678230724355698739 84851323017346086533548109)
        ·
          refine ⟨31819246131504782450080541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84851323017346086533548109 31819246131504782450080541)
          ·
            refine ⟨11932217299314293418780203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31819246131504782450080541 11932217299314293418780203)
            ·
              refine ⟨17898325948971440128170305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11932217299314293418780203 17898325948971440128170305)
              ·
                refine ⟨13423744461728580096127729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17898325948971440128170305 13423744461728580096127729)
                ·
                  refine ⟨10067808346296435072095797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13423744461728580096127729 10067808346296435072095797)
                  ·
                    refine ⟨943857032465290788008981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10067808346296435072095797 943857032465290788008981)
                    ·
                      rfl

theorem cell23_5514465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_5514465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514465 prefixEnd_5514465 := by exact prefixLift 5514465
  have htrace : WordTrace (prefixWord ++ tailWord_5514465) baseStart_5514465 baseEnd_5514465 := by
    simpa [prefixWord, tailWord_5514465, baseEnd_5514465] using wordTrace_append hprefix tailTrace_5514465
  have hstable : (prefixWord ++ tailWord_5514465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514465).length < 2 ^ (prefixWord ++ tailWord_5514465).sum := by decide
  have hdescent : baseEnd_5514465 < baseStart_5514465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514469 : List Nat := [1, 3, 1, 4, 3, 1, 3, 2, 5]
def baseStart_5514469 : Nat := 118140960795 + 5514469 * 2 ^ 59
def prefixEnd_5514469 : Nat := 4983230072969 + 3 ^ 40 * 5514469 * 2
def baseEnd_5514469 : Nat := 314619239035387816486325

theorem tailTrace_5514469 : CollatzResearch.WordTrace tailWord_5514469 prefixEnd_5514469 314619239035387816486325 := by
  unfold tailWord_5514469
  simp only [CollatzResearch.WordTrace]
  refine ⟨201129207859028084170074461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134086138572685389446716307 201129207859028084170074461)
  ·
    refine ⟨75423452947135531563777923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201129207859028084170074461 75423452947135531563777923)
    ·
      refine ⟨113135179420703297345666885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75423452947135531563777923 113135179420703297345666885)
      ·
        refine ⟨21212846141381868252312541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113135179420703297345666885 21212846141381868252312541)
        ·
          refine ⟨7954817303018200594617203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21212846141381868252312541 7954817303018200594617203)
          ·
            refine ⟨11932225954527300891925805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7954817303018200594617203 11932225954527300891925805)
            ·
              refine ⟨4474584732947737834472177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11932225954527300891925805 4474584732947737834472177)
              ·
                refine ⟨3355938549710803375854133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474584732947737834472177 3355938549710803375854133)
                ·
                  refine ⟨314619239035387816486325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3355938549710803375854133 314619239035387816486325)
                  ·
                    rfl

theorem cell23_5514469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_5514469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514469 prefixEnd_5514469 := by exact prefixLift 5514469
  have htrace : WordTrace (prefixWord ++ tailWord_5514469) baseStart_5514469 baseEnd_5514469 := by
    simpa [prefixWord, tailWord_5514469, baseEnd_5514469] using wordTrace_append hprefix tailTrace_5514469
  have hstable : (prefixWord ++ tailWord_5514469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514469).length < 2 ^ (prefixWord ++ tailWord_5514469).sum := by decide
  have hdescent : baseEnd_5514469 < baseStart_5514469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514522 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_5514522 : Nat := 118140960795 + 5514522 * 2 ^ 59
def prefixEnd_5514522 : Nat := 4983230072969 + 3 ^ 40 * 5514522 * 2
def baseEnd_5514522 : Nat := 2831600365793178641014181

theorem tailTrace_5514522 : CollatzResearch.WordTrace tailWord_5514522 prefixEnd_5514522 2831600365793178641014181 := by
  unfold tailWord_5514522
  simp only [CollatzResearch.WordTrace]
  refine ⟨50282785231959018555438455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134087427285224049481169213 50282785231959018555438455)
  ·
    refine ⟨75424177847938527833157683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50282785231959018555438455 75424177847938527833157683)
    ·
      refine ⟨113136266771907791749736525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75424177847938527833157683 113136266771907791749736525)
      ·
        refine ⟨42426100039465421906151197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113136266771907791749736525 42426100039465421906151197)
        ·
          refine ⟨15909787514799533214806699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42426100039465421906151197 15909787514799533214806699)
          ·
            refine ⟨23864681272199299822210049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15909787514799533214806699 23864681272199299822210049)
            ·
              refine ⟨17898510954149474866657537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23864681272199299822210049 17898510954149474866657537)
              ·
                refine ⟨13423883215612106149993153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17898510954149474866657537 13423883215612106149993153)
                ·
                  refine ⟨10067912411709079612494865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13423883215612106149993153 10067912411709079612494865)
                  ·
                    refine ⟨7550934308781809709371149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10067912411709079612494865 7550934308781809709371149)
                    ·
                      refine ⟨2831600365793178641014181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550934308781809709371149 2831600365793178641014181)
                      ·
                        rfl

theorem cell23_5514522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_5514522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514522 prefixEnd_5514522 := by exact prefixLift 5514522
  have htrace : WordTrace (prefixWord ++ tailWord_5514522) baseStart_5514522 baseEnd_5514522 := by
    simpa [prefixWord, tailWord_5514522, baseEnd_5514522] using wordTrace_append hprefix tailTrace_5514522
  have hstable : (prefixWord ++ tailWord_5514522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514522).length < 2 ^ (prefixWord ++ tailWord_5514522).sum := by decide
  have hdescent : baseEnd_5514522 < baseStart_5514522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514569 : List Nat := [1, 2, 1, 1, 2, 3, 3, 5, 1, 1, 3]
def baseStart_5514569 : Nat := 118140960795 + 5514569 * 2 ^ 59
def prefixEnd_5514569 : Nat := 4983230072969 + 3 ^ 40 * 5514569 * 2
def baseEnd_5514569 : Nat := 2831624499383939957126465

theorem tailTrace_5514569 : CollatzResearch.WordTrace tailWord_5514569 prefixEnd_5514569 2831624499383939957126465 := by
  unfold tailWord_5514569
  simp only [CollatzResearch.WordTrace]
  refine ⟨201132855158665801248714761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134088570105777200832476507 201132855158665801248714761)
  ·
    refine ⟨150849641368999350936536071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201132855158665801248714761 150849641368999350936536071)
    ·
      refine ⟨226274462053499026404804107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150849641368999350936536071 226274462053499026404804107)
      ·
        refine ⟨339411693080248539607206161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226274462053499026404804107 339411693080248539607206161)
        ·
          refine ⟨254558769810186404705404621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339411693080248539607206161 254558769810186404705404621)
          ·
            refine ⟨95459538678819901764526733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254558769810186404705404621 95459538678819901764526733)
            ·
              refine ⟨35797327004557463161697525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95459538678819901764526733 35797327004557463161697525)
              ·
                refine ⟨3355999406677262171409143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35797327004557463161697525 3355999406677262171409143)
                ·
                  refine ⟨5033999110015893257113715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355999406677262171409143 5033999110015893257113715)
                  ·
                    refine ⟨7550998665023839885670573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5033999110015893257113715 7550998665023839885670573)
                    ·
                      refine ⟨2831624499383939957126465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7550998665023839885670573 2831624499383939957126465)
                      ·
                        rfl

theorem cell23_5514569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 1, 3].length) (baseStart_5514569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514569 prefixEnd_5514569 := by exact prefixLift 5514569
  have htrace : WordTrace (prefixWord ++ tailWord_5514569) baseStart_5514569 baseEnd_5514569 := by
    simpa [prefixWord, tailWord_5514569, baseEnd_5514569] using wordTrace_append hprefix tailTrace_5514569
  have hstable : (prefixWord ++ tailWord_5514569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514569).length < 2 ^ (prefixWord ++ tailWord_5514569).sum := by decide
  have hdescent : baseEnd_5514569 < baseStart_5514569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514572 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_5514572 : Nat := 118140960795 + 5514572 * 2 ^ 59
def prefixEnd_5514572 : Nat := 4983230072969 + 3 ^ 40 * 5514572 * 2
def baseEnd_5514572 : Nat := 943875346608634481796317

theorem tailTrace_5514572 : CollatzResearch.WordTrace tailWord_5514572 prefixEnd_5514572 943875346608634481796317 := by
  unfold tailWord_5514572
  simp only [CollatzResearch.WordTrace]
  refine ⟨100566482288827466380536985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134088643051769955174049313 100566482288827466380536985)
  ·
    refine ⟨75424861716620599785402739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100566482288827466380536985 75424861716620599785402739)
    ·
      refine ⟨113137292574930899678104109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75424861716620599785402739 113137292574930899678104109)
      ·
        refine ⟨42426484715599087379289041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113137292574930899678104109 42426484715599087379289041)
        ·
          refine ⟨31819863536699315534466781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42426484715599087379289041 31819863536699315534466781)
          ·
            refine ⟨11932448826262243325425043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31819863536699315534466781 11932448826262243325425043)
            ·
              refine ⟨17898673239393364988137565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11932448826262243325425043 17898673239393364988137565)
              ·
                refine ⟨6712002464772511870551587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17898673239393364988137565 6712002464772511870551587)
                ·
                  refine ⟨10068003697158767805827381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6712002464772511870551587 10068003697158767805827381)
                  ·
                    refine ⟨943875346608634481796317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10068003697158767805827381 943875346608634481796317)
                    ·
                      rfl

theorem cell23_5514572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_5514572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514572 prefixEnd_5514572 := by exact prefixLift 5514572
  have htrace : WordTrace (prefixWord ++ tailWord_5514572) baseStart_5514572 baseEnd_5514572 := by
    simpa [prefixWord, tailWord_5514572, baseEnd_5514572] using wordTrace_append hprefix tailTrace_5514572
  have hstable : (prefixWord ++ tailWord_5514572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514572).length < 2 ^ (prefixWord ++ tailWord_5514572).sum := by decide
  have hdescent : baseEnd_5514572 < baseStart_5514572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514595 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 5]
def baseStart_5514595 : Nat := 118140960795 + 5514595 * 2 ^ 59
def prefixEnd_5514595 : Nat := 4983230072969 + 3 ^ 40 * 5514595 * 2
def baseEnd_5514595 : Nat := 2831637849880956855401345

theorem tailTrace_5514595 : CollatzResearch.WordTrace tailWord_5514595 prefixEnd_5514595 2831637849880956855401345 := by
  unfold tailWord_5514595
  simp only [CollatzResearch.WordTrace]
  refine ⟨201133803456571607689161239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134089202304381071792774159 201133803456571607689161239)
  ·
    refine ⟨301700705184857411533741859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201133803456571607689161239 301700705184857411533741859)
    ·
      refine ⟨452551057777286117300612789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301700705184857411533741859 452551057777286117300612789)
      ·
        refine ⟨42426661666620573496932449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 452551057777286117300612789 42426661666620573496932449)
        ·
          refine ⟨31819996249965430122699337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42426661666620573496932449 31819996249965430122699337)
          ·
            refine ⟨23864997187474072592024503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31819996249965430122699337 23864997187474072592024503)
            ·
              refine ⟨35797495781211108888036755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23864997187474072592024503 35797495781211108888036755)
              ·
                refine ⟨53696243671816663332055133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35797495781211108888036755 53696243671816663332055133)
                ·
                  refine ⟨20136091376931248749520675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53696243671816663332055133 20136091376931248749520675)
                  ·
                    refine ⟨30204137065396873124281013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20136091376931248749520675 30204137065396873124281013)
                    ·
                      refine ⟨2831637849880956855401345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30204137065396873124281013 2831637849880956855401345)
                      ·
                        rfl

theorem cell23_5514595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_5514595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514595 prefixEnd_5514595 := by exact prefixLift 5514595
  have htrace : WordTrace (prefixWord ++ tailWord_5514595) baseStart_5514595 baseEnd_5514595 := by
    simpa [prefixWord, tailWord_5514595, baseEnd_5514595] using wordTrace_append hprefix tailTrace_5514595
  have hstable : (prefixWord ++ tailWord_5514595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514595).length < 2 ^ (prefixWord ++ tailWord_5514595).sum := by decide
  have hdescent : baseEnd_5514595 < baseStart_5514595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514606 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_5514606 : Nat := 118140960795 + 5514606 * 2 ^ 59
def prefixEnd_5514606 : Nat := 4983230072969 + 3 ^ 40 * 5514606 * 2
def baseEnd_5514606 : Nat := 943881166056052104121265

theorem tailTrace_5514606 : CollatzResearch.WordTrace tailWord_5514606 prefixEnd_5514606 943881166056052104121265 := by
  unfold tailWord_5514606
  simp only [CollatzResearch.WordTrace]
  refine ⟨25141775582441469570976459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134089469773021171045207781 25141775582441469570976459)
  ·
    refine ⟨37712663373662204356464689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25141775582441469570976459 37712663373662204356464689)
    ·
      refine ⟨28284497530246653267348517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37712663373662204356464689 28284497530246653267348517)
      ·
        refine ⟨5303343286921247487627847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28284497530246653267348517 5303343286921247487627847)
        ·
          refine ⟨7955014930381871231441771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5303343286921247487627847 7955014930381871231441771)
          ·
            refine ⟨11932522395572806847162657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7955014930381871231441771 11932522395572806847162657)
            ·
              refine ⟨8949391796679605135371993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11932522395572806847162657 8949391796679605135371993)
              ·
                refine ⟨6712043847509703851528995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8949391796679605135371993 6712043847509703851528995)
                ·
                  refine ⟨10068065771264555777293493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6712043847509703851528995 10068065771264555777293493)
                  ·
                    refine ⟨943881166056052104121265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10068065771264555777293493 943881166056052104121265)
                    ·
                      rfl

theorem cell23_5514606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_5514606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514606 prefixEnd_5514606 := by exact prefixLift 5514606
  have htrace : WordTrace (prefixWord ++ tailWord_5514606) baseStart_5514606 baseEnd_5514606 := by
    simpa [prefixWord, tailWord_5514606, baseEnd_5514606] using wordTrace_append hprefix tailTrace_5514606
  have hstable : (prefixWord ++ tailWord_5514606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514606).length < 2 ^ (prefixWord ++ tailWord_5514606).sum := by decide
  have hdescent : baseEnd_5514606 < baseStart_5514606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514609 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 3, 2, 2]
def baseStart_5514609 : Nat := 118140960795 + 5514609 * 2 ^ 59
def prefixEnd_5514609 : Nat := 4983230072969 + 3 ^ 40 * 5514609 * 2
def baseEnd_5514609 : Nat := 2831645038610119800626281

theorem tailTrace_5514609 : CollatzResearch.WordTrace tailWord_5514609 prefixEnd_5514609 2831645038610119800626281 := by
  unfold tailWord_5514609
  simp only [CollatzResearch.WordTrace]
  refine ⟨201134314078520888080170881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134089542719013925386780587 201134314078520888080170881)
  ·
    refine ⟨150850735558890666060128161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201134314078520888080170881 150850735558890666060128161)
    ·
      refine ⟨113138051669167999545096121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150850735558890666060128161 113138051669167999545096121)
      ·
        refine ⟨84853538751875999658822091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113138051669167999545096121 84853538751875999658822091)
        ·
          refine ⟨127280308127813999488233137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84853538751875999658822091 127280308127813999488233137)
          ·
            refine ⟨95460231095860499616174853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127280308127813999488233137 95460231095860499616174853)
            ·
              refine ⟨17898793330473843678032785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95460231095860499616174853 17898793330473843678032785)
              ·
                refine ⟨13424094997855382758524589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17898793330473843678032785 13424094997855382758524589)
                ·
                  refine ⟨5034035624195768534446721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13424094997855382758524589 5034035624195768534446721)
                  ·
                    refine ⟨3775526718146826400835041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5034035624195768534446721 3775526718146826400835041)
                    ·
                      refine ⟨2831645038610119800626281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775526718146826400835041 2831645038610119800626281)
                      ·
                        rfl

theorem cell23_5514609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_5514609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514609 prefixEnd_5514609 := by exact prefixLift 5514609
  have htrace : WordTrace (prefixWord ++ tailWord_5514609) baseStart_5514609 baseEnd_5514609 := by
    simpa [prefixWord, tailWord_5514609, baseEnd_5514609] using wordTrace_append hprefix tailTrace_5514609
  have hstable : (prefixWord ++ tailWord_5514609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514609).length < 2 ^ (prefixWord ++ tailWord_5514609).sum := by decide
  have hdescent : baseEnd_5514609 < baseStart_5514609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514626 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_5514626 : Nat := 118140960795 + 5514626 * 2 ^ 59
def prefixEnd_5514626 : Nat := 4983230072969 + 3 ^ 40 * 5514626 * 2
def baseEnd_5514626 : Nat := 2831653767781246234113703

theorem tailTrace_5514626 : CollatzResearch.WordTrace tailWord_5514626 prefixEnd_5514626 2831653767781246234113703 := by
  unfold tailWord_5514626
  simp only [CollatzResearch.WordTrace]
  refine ⟨50283733529864824995884933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134089956079639533322359821 50283733529864824995884933)
  ·
    refine ⟨9428200036849654686728425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50283733529864824995884933 9428200036849654686728425)
    ·
      refine ⟨7071150027637241015046319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9428200036849654686728425 7071150027637241015046319)
      ·
        refine ⟨10606725041455861522569479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071150027637241015046319 10606725041455861522569479)
        ·
          refine ⟨15910087562183792283854219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10606725041455861522569479 15910087562183792283854219)
          ·
            refine ⟨23865131343275688425781329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15910087562183792283854219 23865131343275688425781329)
            ·
              refine ⟨17898848507456766319335997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23865131343275688425781329 17898848507456766319335997)
              ·
                refine ⟨6712068190296287369750999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17898848507456766319335997 6712068190296287369750999)
                ·
                  refine ⟨10068102285444431054626499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6712068190296287369750999 10068102285444431054626499)
                  ·
                    refine ⟨15102153428166646581939749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10068102285444431054626499 15102153428166646581939749)
                    ·
                      refine ⟨2831653767781246234113703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15102153428166646581939749 2831653767781246234113703)
                      ·
                        rfl

theorem cell23_5514626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_5514626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514626 prefixEnd_5514626 := by exact prefixLift 5514626
  have htrace : WordTrace (prefixWord ++ tailWord_5514626) baseStart_5514626 baseEnd_5514626 := by
    simpa [prefixWord, tailWord_5514626, baseEnd_5514626] using wordTrace_append hprefix tailTrace_5514626
  have hstable : (prefixWord ++ tailWord_5514626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514626).length < 2 ^ (prefixWord ++ tailWord_5514626).sum := by decide
  have hdescent : baseEnd_5514626 < baseStart_5514626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514659 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 3]
def baseStart_5514659 : Nat := 118140960795 + 5514659 * 2 ^ 59
def prefixEnd_5514659 : Nat := 4983230072969 + 3 ^ 40 * 5514659 * 2
def baseEnd_5514659 : Nat := 2831670712642844605001051

theorem tailTrace_5514659 : CollatzResearch.WordTrace tailWord_5514659 prefixEnd_5514659 2831670712642844605001051 := by
  unfold tailWord_5514659
  simp only [CollatzResearch.WordTrace]
  refine ⟨201136137728339746619491031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134090758485559831079660687 201136137728339746619491031)
  ·
    refine ⟨301704206592509619929236547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201136137728339746619491031 301704206592509619929236547)
    ·
      refine ⟨452556309888764429893854821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301704206592509619929236547 452556309888764429893854821)
      ·
        refine ⟨84854308104143330605097779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 452556309888764429893854821 84854308104143330605097779)
        ·
          refine ⟨127281462156214995907646669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84854308104143330605097779 127281462156214995907646669)
          ·
            refine ⟨47730548308580623465367501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127281462156214995907646669 47730548308580623465367501)
            ·
              refine ⟨17898955615717733799512813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47730548308580623465367501 17898955615717733799512813)
              ·
                refine ⟨6712108355894150174817305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17898955615717733799512813 6712108355894150174817305)
                ·
                  refine ⟨5034081266920612631112979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6712108355894150174817305 5034081266920612631112979)
                  ·
                    refine ⟨7551121900380918946669469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5034081266920612631112979 7551121900380918946669469)
                    ·
                      refine ⟨2831670712642844605001051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7551121900380918946669469 2831670712642844605001051)
                      ·
                        rfl

theorem cell23_5514659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_5514659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514659 prefixEnd_5514659 := by exact prefixLift 5514659
  have htrace : WordTrace (prefixWord ++ tailWord_5514659) baseStart_5514659 baseEnd_5514659 := by
    simpa [prefixWord, tailWord_5514659, baseEnd_5514659] using wordTrace_append hprefix tailTrace_5514659
  have hstable : (prefixWord ++ tailWord_5514659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514659).length < 2 ^ (prefixWord ++ tailWord_5514659).sum := by decide
  have hdescent : baseEnd_5514659 < baseStart_5514659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514699 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 4, 2, 2]
def baseStart_5514699 : Nat := 118140960795 + 5514699 * 2 ^ 59
def prefixEnd_5514699 : Nat := 4983230072969 + 3 ^ 40 * 5514699 * 2
def baseEnd_5514699 : Nat := 2831691251869024448500867

theorem tailTrace_5514699 : CollatzResearch.WordTrace tailWord_5514699 prefixEnd_5514699 2831691251869024448500867 := by
  unfold tailWord_5514699
  simp only [CollatzResearch.WordTrace]
  refine ⟨201137596648194833450947151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134091731098796555633964767 201137596648194833450947151)
  ·
    refine ⟨301706394972292250176420727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201137596648194833450947151 301706394972292250176420727)
    ·
      refine ⟨452559592458438375264631091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301706394972292250176420727 452559592458438375264631091)
      ·
        refine ⟨678839388687657562896946637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452559592458438375264631091 678839388687657562896946637)
        ·
          refine ⟨254564770757871586086354989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 678839388687657562896946637 254564770757871586086354989)
          ·
            refine ⟨95461789034201844782383121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254564770757871586086354989 95461789034201844782383121)
            ·
              refine ⟨71596341775651383586787341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95461789034201844782383121 71596341775651383586787341)
              ·
                refine ⟨26848628165869268845045253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71596341775651383586787341 26848628165869268845045253)
                ·
                  refine ⟨5034117781100487908445985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26848628165869268845045253 5034117781100487908445985)
                  ·
                    refine ⟨3775588335825365931334489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5034117781100487908445985 3775588335825365931334489)
                    ·
                      refine ⟨2831691251869024448500867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775588335825365931334489 2831691251869024448500867)
                      ·
                        rfl

theorem cell23_5514699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 2, 2].length) (baseStart_5514699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514699 prefixEnd_5514699 := by exact prefixLift 5514699
  have htrace : WordTrace (prefixWord ++ tailWord_5514699) baseStart_5514699 baseEnd_5514699 := by
    simpa [prefixWord, tailWord_5514699, baseEnd_5514699] using wordTrace_append hprefix tailTrace_5514699
  have hstable : (prefixWord ++ tailWord_5514699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514699).length < 2 ^ (prefixWord ++ tailWord_5514699).sum := by decide
  have hdescent : baseEnd_5514699 < baseStart_5514699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514702 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_5514702 : Nat := 118140960795 + 5514702 * 2 ^ 59
def prefixEnd_5514702 : Nat := 4983230072969 + 3 ^ 40 * 5514702 * 2
def baseEnd_5514702 : Nat := 2831692792310987936763353

theorem tailTrace_5514702 : CollatzResearch.WordTrace tailWord_5514702 prefixEnd_5514702 2831692792310987936763353 := by
  unfold tailWord_5514702
  simp only [CollatzResearch.WordTrace]
  refine ⟨25142213258397995620413295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134091804044789309975537573 25142213258397995620413295)
  ·
    refine ⟨37713319887596993430619943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25142213258397995620413295 37713319887596993430619943)
    ·
      refine ⟨56569979831395490145929915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37713319887596993430619943 56569979831395490145929915)
      ·
        refine ⟨84854969747093235218894873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56569979831395490145929915 84854969747093235218894873)
        ·
          refine ⟨63641227310319926414171155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84854969747093235218894873 63641227310319926414171155)
          ·
            refine ⟨95461840965479889621256733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63641227310319926414171155 95461840965479889621256733)
            ·
              refine ⟨35798190362054958607971275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95461840965479889621256733 35798190362054958607971275)
              ·
                refine ⟨53697285543082437911956913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35798190362054958607971275 53697285543082437911956913)
                ·
                  refine ⟨40272964157311828433967685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53697285543082437911956913 40272964157311828433967685)
                  ·
                    refine ⟨7551180779495967831368941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40272964157311828433967685 7551180779495967831368941)
                    ·
                      refine ⟨2831692792310987936763353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7551180779495967831368941 2831692792310987936763353)
                      ·
                        rfl

theorem cell23_5514702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_5514702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514702 prefixEnd_5514702 := by exact prefixLift 5514702
  have htrace : WordTrace (prefixWord ++ tailWord_5514702) baseStart_5514702 baseEnd_5514702 := by
    simpa [prefixWord, tailWord_5514702, baseEnd_5514702] using wordTrace_append hprefix tailTrace_5514702
  have hstable : (prefixWord ++ tailWord_5514702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514702).length < 2 ^ (prefixWord ++ tailWord_5514702).sum := by decide
  have hdescent : baseEnd_5514702 < baseStart_5514702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514750 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5514750 : Nat := 118140960795 + 5514750 * 2 ^ 59
def prefixEnd_5514750 : Nat := 4983230072969 + 3 ^ 40 * 5514750 * 2
def baseEnd_5514750 : Nat := 2831717439382403748963133

theorem tailTrace_5514750 : CollatzResearch.WordTrace tailWord_5514750 prefixEnd_5514750 2831717439382403748963133 := by
  unfold tailWord_5514750
  simp only [CollatzResearch.WordTrace]
  refine ⟨25142432096376258645131713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134092971180673379440702469 25142432096376258645131713)
  ·
    refine ⟨18856824072282193983848785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25142432096376258645131713 18856824072282193983848785)
    ·
      refine ⟨14142618054211645487886589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18856824072282193983848785 14142618054211645487886589)
      ·
        refine ⟨5303481770329367057957471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14142618054211645487886589 5303481770329367057957471)
        ·
          refine ⟨7955222655494050586936207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5303481770329367057957471 7955222655494050586936207)
          ·
            refine ⟨11932833983241075880404311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7955222655494050586936207 11932833983241075880404311)
            ·
              refine ⟨17899250974861613820606467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11932833983241075880404311 17899250974861613820606467)
              ·
                refine ⟨26848876462292420730909701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17899250974861613820606467 26848876462292420730909701)
                ·
                  refine ⟨5034164336679828887045569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26848876462292420730909701 5034164336679828887045569)
                  ·
                    refine ⟨3775623252509871665284177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5034164336679828887045569 3775623252509871665284177)
                    ·
                      refine ⟨2831717439382403748963133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775623252509871665284177 2831717439382403748963133)
                      ·
                        rfl

theorem cell23_5514750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5514750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514750 prefixEnd_5514750 := by exact prefixLift 5514750
  have htrace : WordTrace (prefixWord ++ tailWord_5514750) baseStart_5514750 baseEnd_5514750 := by
    simpa [prefixWord, tailWord_5514750, baseEnd_5514750] using wordTrace_append hprefix tailTrace_5514750
  have hstable : (prefixWord ++ tailWord_5514750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514750).length < 2 ^ (prefixWord ++ tailWord_5514750).sum := by decide
  have hdescent : baseEnd_5514750 < baseStart_5514750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514809 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 3]
def baseStart_5514809 : Nat := 118140960795 + 5514809 * 2 ^ 59
def prefixEnd_5514809 : Nat := 4983230072969 + 3 ^ 40 * 5514809 * 2
def baseEnd_5514809 : Nat := 2831747734741019018125361

theorem tailTrace_5514809 : CollatzResearch.WordTrace tailWord_5514809 prefixEnd_5514809 2831747734741019018125361 := by
  unfold tailWord_5514809
  simp only [CollatzResearch.WordTrace]
  refine ⟨201141608677796322237451481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134094405785197548158300987 201141608677796322237451481)
  ·
    refine ⟨150856206508347241678088611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201141608677796322237451481 150856206508347241678088611)
    ·
      refine ⟨226284309762520862517132917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150856206508347241678088611 226284309762520862517132917)
      ·
        refine ⟨21214154040236330860981211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226284309762520862517132917 21214154040236330860981211)
        ·
          refine ⟨31821231060354496291471817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21214154040236330860981211 31821231060354496291471817)
          ·
            refine ⟨23865923295265872218603863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31821231060354496291471817 23865923295265872218603863)
            ·
              refine ⟨35798884942898808327905795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23865923295265872218603863 35798884942898808327905795)
              ·
                refine ⟨53698327414348212491858693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35798884942898808327905795 53698327414348212491858693)
                ·
                  refine ⟨10068436390190289842223505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53698327414348212491858693 10068436390190289842223505)
                  ·
                    refine ⟨7551327292642717381667629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10068436390190289842223505 7551327292642717381667629)
                    ·
                      refine ⟨2831747734741019018125361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7551327292642717381667629 2831747734741019018125361)
                      ·
                        rfl

theorem cell23_5514809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_5514809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514809 prefixEnd_5514809 := by exact prefixLift 5514809
  have htrace : WordTrace (prefixWord ++ tailWord_5514809) baseStart_5514809 baseEnd_5514809 := by
    simpa [prefixWord, tailWord_5514809, baseEnd_5514809] using wordTrace_append hprefix tailTrace_5514809
  have hstable : (prefixWord ++ tailWord_5514809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514809).length < 2 ^ (prefixWord ++ tailWord_5514809).sum := by decide
  have hdescent : baseEnd_5514809 < baseStart_5514809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514873 : List Nat := [1, 2, 1, 3, 3, 1, 3, 4, 1, 1, 3]
def baseStart_5514873 : Nat := 118140960795 + 5514873 * 2 ^ 59
def prefixEnd_5514873 : Nat := 4983230072969 + 3 ^ 40 * 5514873 * 2
def baseEnd_5514873 : Nat := 2831780597502906767725067

theorem tailTrace_5514873 : CollatzResearch.WordTrace tailWord_5514873 prefixEnd_5514873 2831780597502906767725067 := by
  unfold tailWord_5514873
  simp only [CollatzResearch.WordTrace]
  refine ⟨201143942949564461167781273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134095961966376307445187515 201143942949564461167781273)
  ·
    refine ⟨150857957212173345875835955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201143942949564461167781273 150857957212173345875835955)
    ·
      refine ⟨226286935818260018813753933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150857957212173345875835955 226286935818260018813753933)
      ·
        refine ⟨84857600931847507055157725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226286935818260018813753933 84857600931847507055157725)
        ·
          refine ⟨31821600349442815145684147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84857600931847507055157725 31821600349442815145684147)
          ·
            refine ⟨47732400524164222718526221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31821600349442815145684147 47732400524164222718526221)
            ·
              refine ⟨17899650196561583519447333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47732400524164222718526221 17899650196561583519447333)
              ·
                refine ⟨3356184411855296909896375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17899650196561583519447333 3356184411855296909896375)
                ·
                  refine ⟨5034276617782945364844563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356184411855296909896375 5034276617782945364844563)
                  ·
                    refine ⟨7551414926674418047266845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5034276617782945364844563 7551414926674418047266845)
                    ·
                      refine ⟨2831780597502906767725067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7551414926674418047266845 2831780597502906767725067)
                      ·
                        rfl

theorem cell23_5514873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_5514873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514873 prefixEnd_5514873 := by exact prefixLift 5514873
  have htrace : WordTrace (prefixWord ++ tailWord_5514873) baseStart_5514873 baseEnd_5514873 := by
    simpa [prefixWord, tailWord_5514873, baseEnd_5514873] using wordTrace_append hprefix tailTrace_5514873
  have hstable : (prefixWord ++ tailWord_5514873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514873).length < 2 ^ (prefixWord ++ tailWord_5514873).sum := by decide
  have hdescent : baseEnd_5514873 < baseStart_5514873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514910 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_5514910 : Nat := 118140960795 + 5514910 * 2 ^ 59
def prefixEnd_5514910 : Nat := 4983230072969 + 3 ^ 40 * 5514910 * 2
def baseEnd_5514910 : Nat := 943933198762374374320799

theorem tailTrace_5514910 : CollatzResearch.WordTrace tailWord_5514910 prefixEnd_5514910 943933198762374374320799 := by
  unfold tailWord_5514910
  simp only [CollatzResearch.WordTrace]
  refine ⟨25143161556303802060859773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134096861633620277657918789 25143161556303802060859773)
  ·
    refine ⟨9428685583613925772822415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25143161556303802060859773 9428685583613925772822415)
    ·
      refine ⟨14143028375420888659233623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9428685583613925772822415 14143028375420888659233623)
      ·
        refine ⟨21214542563131332988850435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14143028375420888659233623 21214542563131332988850435)
        ·
          refine ⟨31821813844696999483275653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21214542563131332988850435 31821813844696999483275653)
          ·
            refine ⟨5966590095880687403114185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31821813844696999483275653 5966590095880687403114185)
            ·
              refine ⟨4474942571910515552335639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5966590095880687403114185 4474942571910515552335639)
              ·
                refine ⟨6712413857865773328503459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4474942571910515552335639 6712413857865773328503459)
                ·
                  refine ⟨10068620786798659992755189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6712413857865773328503459 10068620786798659992755189)
                  ·
                    refine ⟨943933198762374374320799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10068620786798659992755189 943933198762374374320799)
                    ·
                      rfl

theorem cell23_5514910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_5514910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514910 prefixEnd_5514910 := by exact prefixLift 5514910
  have htrace : WordTrace (prefixWord ++ tailWord_5514910) baseStart_5514910 baseEnd_5514910 := by
    simpa [prefixWord, tailWord_5514910, baseEnd_5514910] using wordTrace_append hprefix tailTrace_5514910
  have hstable : (prefixWord ++ tailWord_5514910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514910).length < 2 ^ (prefixWord ++ tailWord_5514910).sum := by decide
  have hdescent : baseEnd_5514910 < baseStart_5514910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514913 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_5514913 : Nat := 118140960795 + 5514913 * 2 ^ 59
def prefixEnd_5514913 : Nat := 4983230072969 + 3 ^ 40 * 5514913 * 2
def baseEnd_5514913 : Nat := 2831801136729086611224883

theorem tailTrace_5514913 : CollatzResearch.WordTrace tailWord_5514913 prefixEnd_5514913 2831801136729086611224883 := by
  unfold tailWord_5514913
  simp only [CollatzResearch.WordTrace]
  refine ⟨201145401869419547999237393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134096934579613031999491595 201145401869419547999237393)
  ·
    refine ⟨150859051402064660999428045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201145401869419547999237393 150859051402064660999428045)
    ·
      refine ⟨56572144275774247874785517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150859051402064660999428045 56572144275774247874785517)
      ·
        refine ⟨21214554103415342953044569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56572144275774247874785517 21214554103415342953044569)
        ·
          refine ⟨15910915577561507214783427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21214554103415342953044569 15910915577561507214783427)
          ·
            refine ⟨23866373366342260822175141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15910915577561507214783427 23866373366342260822175141)
            ·
              refine ⟨4474945006189173904157839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23866373366342260822175141 4474945006189173904157839)
              ·
                refine ⟨6712417509283760856236759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4474945006189173904157839 6712417509283760856236759)
                ·
                  refine ⟨10068626263925641284355139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6712417509283760856236759 10068626263925641284355139)
                  ·
                    refine ⟨15102939395888461926532709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10068626263925641284355139 15102939395888461926532709)
                    ·
                      refine ⟨2831801136729086611224883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15102939395888461926532709 2831801136729086611224883)
                      ·
                        rfl

theorem cell23_5514913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_5514913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514913 prefixEnd_5514913 := by exact prefixLift 5514913
  have htrace : WordTrace (prefixWord ++ tailWord_5514913) baseStart_5514913 baseEnd_5514913 := by
    simpa [prefixWord, tailWord_5514913, baseEnd_5514913] using wordTrace_append hprefix tailTrace_5514913
  have hstable : (prefixWord ++ tailWord_5514913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514913).length < 2 ^ (prefixWord ++ tailWord_5514913).sum := by decide
  have hdescent : baseEnd_5514913 < baseStart_5514913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514930 : List Nat := [3, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_5514930 : Nat := 118140960795 + 5514930 * 2 ^ 59
def prefixEnd_5514930 : Nat := 4983230072969 + 3 ^ 40 * 5514930 * 2
def baseEnd_5514930 : Nat := 2831809865900213044712305

theorem tailTrace_5514930 : CollatzResearch.WordTrace tailWord_5514930 prefixEnd_5514930 2831809865900213044712305 := by
  unfold tailWord_5514930
  simp only [CollatzResearch.WordTrace]
  refine ⟨50286505477589489975651561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134097347940238639935070829 50286505477589489975651561)
  ·
    refine ⟨37714879108192117481738671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50286505477589489975651561 37714879108192117481738671)
    ·
      refine ⟨56572318662288176222608007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37714879108192117481738671 56572318662288176222608007)
      ·
        refine ⟨84858477993432264333912011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56572318662288176222608007 84858477993432264333912011)
        ·
          refine ⟨127287716990148396500868017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84858477993432264333912011 127287716990148396500868017)
          ·
            refine ⟨95465787742611297375651013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127287716990148396500868017 95465787742611297375651013)
            ·
              refine ⟨17899835201739618257934565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95465787742611297375651013 17899835201739618257934565)
              ·
                refine ⟨3356219100326178423362731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17899835201739618257934565 3356219100326178423362731)
                ·
                  refine ⟨5034328650489267635044097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356219100326178423362731 5034328650489267635044097)
                  ·
                    refine ⟨3775746487866950726283073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5034328650489267635044097 3775746487866950726283073)
                    ·
                      refine ⟨2831809865900213044712305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775746487866950726283073 2831809865900213044712305)
                      ·
                        rfl

theorem cell23_5514930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_5514930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514930 prefixEnd_5514930 := by exact prefixLift 5514930
  have htrace : WordTrace (prefixWord ++ tailWord_5514930) baseStart_5514930 baseEnd_5514930 := by
    simpa [prefixWord, tailWord_5514930, baseEnd_5514930] using wordTrace_append hprefix tailTrace_5514930
  have hstable : (prefixWord ++ tailWord_5514930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514930).length < 2 ^ (prefixWord ++ tailWord_5514930).sum := by decide
  have hdescent : baseEnd_5514930 < baseStart_5514930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514964 : List Nat := [2, 4, 1, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5514964 : Nat := 118140960795 + 5514964 * 2 ^ 59
def prefixEnd_5514964 : Nat := 4983230072969 + 3 ^ 40 * 5514964 * 2
def baseEnd_5514964 : Nat := 2831827324242465911687149

theorem tailTrace_5514964 : CollatzResearch.WordTrace tailWord_5514964 prefixEnd_5514964 2831827324242465911687149 := by
  unfold tailWord_5514964
  simp only [CollatzResearch.WordTrace]
  refine ⟨100573630996117391854671973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134098174661489855806229297 100573630996117391854671973)
  ·
    refine ⟨18857555811772010972750995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100573630996117391854671973 18857555811772010972750995)
    ·
      refine ⟨28286333717658016459126493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18857555811772010972750995 28286333717658016459126493)
      ·
        refine ⟨10607375144121756172172435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28286333717658016459126493 10607375144121756172172435)
        ·
          refine ⟨15911062716182634258258653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10607375144121756172172435 15911062716182634258258653)
          ·
            refine ⟨5966648518568487846846995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15911062716182634258258653 5966648518568487846846995)
            ·
              refine ⟨8949972777852731770270493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5966648518568487846846995 8949972777852731770270493)
              ·
                refine ⟨3356239791694774413851435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8949972777852731770270493 3356239791694774413851435)
                ·
                  refine ⟨5034359687542161620777153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356239791694774413851435 5034359687542161620777153)
                  ·
                    refine ⟨3775769765656621215582865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5034359687542161620777153 3775769765656621215582865)
                    ·
                      refine ⟨2831827324242465911687149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775769765656621215582865 2831827324242465911687149)
                      ·
                        rfl

theorem cell23_5514964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5514964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514964 prefixEnd_5514964 := by exact prefixLift 5514964
  have htrace : WordTrace (prefixWord ++ tailWord_5514964) baseStart_5514964 baseEnd_5514964 := by
    simpa [prefixWord, tailWord_5514964, baseEnd_5514964] using wordTrace_append hprefix tailTrace_5514964
  have hstable : (prefixWord ++ tailWord_5514964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514964).length < 2 ^ (prefixWord ++ tailWord_5514964).sum := by decide
  have hdescent : baseEnd_5514964 < baseStart_5514964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514999 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_5514999 : Nat := 118140960795 + 5514999 * 2 ^ 59
def prefixEnd_5514999 : Nat := 4983230072969 + 3 ^ 40 * 5514999 * 2
def baseEnd_5514999 : Nat := 2831845296065373274749487

theorem tailTrace_5514999 : CollatzResearch.WordTrace tailWord_5514999 prefixEnd_5514999 2831845296065373274749487 := by
  unfold tailWord_5514999
  simp only [CollatzResearch.WordTrace]
  refine ⟨201148538547107984686868051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134099025698071989791245367 201148538547107984686868051)
  ·
    refine ⟨301722807820661977030302077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201148538547107984686868051 301722807820661977030302077)
    ·
      refine ⟨113146052932748241386363279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301722807820661977030302077 113146052932748241386363279)
      ·
        refine ⟨169719079399122362079544919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113146052932748241386363279 169719079399122362079544919)
        ·
          refine ⟨254578619098683543119317379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169719079399122362079544919 254578619098683543119317379)
          ·
            refine ⟨381867928648025314678976069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254578619098683543119317379 381867928648025314678976069)
            ·
              refine ⟨71600236621504746502308013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 381867928648025314678976069 71600236621504746502308013)
              ·
                refine ⟨26850088733064279938365505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71600236621504746502308013 26850088733064279938365505)
                ·
                  refine ⟨20137566549798209953774129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26850088733064279938365505 20137566549798209953774129)
                  ·
                    refine ⟨15103174912348657465330597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20137566549798209953774129 15103174912348657465330597)
                    ·
                      refine ⟨2831845296065373274749487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15103174912348657465330597 2831845296065373274749487)
                      ·
                        rfl

theorem cell23_5514999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_5514999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5514999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5514999 prefixEnd_5514999 := by exact prefixLift 5514999
  have htrace : WordTrace (prefixWord ++ tailWord_5514999) baseStart_5514999 baseEnd_5514999 := by
    simpa [prefixWord, tailWord_5514999, baseEnd_5514999] using wordTrace_append hprefix tailTrace_5514999
  have hstable : (prefixWord ++ tailWord_5514999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514999).length < 2 ^ (prefixWord ++ tailWord_5514999).sum := by decide
  have hdescent : baseEnd_5514999 < baseStart_5514999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515009 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 7]
def baseStart_5515009 : Nat := 118140960795 + 5515009 * 2 ^ 59
def prefixEnd_5515009 : Nat := 4983230072969 + 3 ^ 40 * 5515009 * 2
def baseEnd_5515009 : Nat := 314650047874657581736049

theorem tailTrace_5515009 : CollatzResearch.WordTrace tailWord_5515009 prefixEnd_5515009 314650047874657581736049 := by
  unfold tailWord_5515009
  simp only [CollatzResearch.WordTrace]
  refine ⟨201148903277071756394732081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134099268851381170929821387 201148903277071756394732081)
  ·
    refine ⟨150861677457803817296049061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201148903277071756394732081 150861677457803817296049061)
    ·
      refine ⟨28286564523338215743009199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150861677457803817296049061 28286564523338215743009199)
      ·
        refine ⟨42429846785007323614513799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28286564523338215743009199 42429846785007323614513799)
        ·
          refine ⟨63644770177510985421770699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42429846785007323614513799 63644770177510985421770699)
          ·
            refine ⟨95467155266266478132656049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63644770177510985421770699 95467155266266478132656049)
            ·
              refine ⟨71600366449699858599492037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95467155266266478132656049 71600366449699858599492037)
              ·
                refine ⟨13425068709318723487404757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71600366449699858599492037 13425068709318723487404757)
                ·
                  refine ⟨314650047874657581736049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13425068709318723487404757 314650047874657581736049)
                  ·
                    rfl

theorem cell23_5515009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 7].length) (baseStart_5515009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515009 prefixEnd_5515009 := by exact prefixLift 5515009
  have htrace : WordTrace (prefixWord ++ tailWord_5515009) baseStart_5515009 baseEnd_5515009 := by
    simpa [prefixWord, tailWord_5515009, baseEnd_5515009] using wordTrace_append hprefix tailTrace_5515009
  have hstable : (prefixWord ++ tailWord_5515009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515009).length < 2 ^ (prefixWord ++ tailWord_5515009).sum := by decide
  have hdescent : baseEnd_5515009 < baseStart_5515009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515036 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_5515036 : Nat := 118140960795 + 5515036 * 2 ^ 59
def prefixEnd_5515036 : Nat := 4983230072969 + 3 ^ 40 * 5515036 * 2
def baseEnd_5515036 : Nat := 2831864294849589629986817

theorem tailTrace_5515036 : CollatzResearch.WordTrace tailWord_5515036 prefixEnd_5515036 2831864294849589629986817 := by
  unfold tailWord_5515036
  simp only [CollatzResearch.WordTrace]
  refine ⟨100574944023986970002982481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134099925365315960003976641 100574944023986970002982481)
  ·
    refine ⟨75431208017990227502236861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100574944023986970002982481 75431208017990227502236861)
    ·
      refine ⟨28286703006746335313338823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75431208017990227502236861 28286703006746335313338823)
      ·
        refine ⟨42430054510119502970008235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28286703006746335313338823 42430054510119502970008235)
        ·
          refine ⟨63645081765179254455012353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42430054510119502970008235 63645081765179254455012353)
          ·
            refine ⟨47733811323884440841259265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63645081765179254455012353 47733811323884440841259265)
            ·
              refine ⟨35800358492913330630944449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47733811323884440841259265 35800358492913330630944449)
              ·
                refine ⟨26850268869684997973208337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35800358492913330630944449 26850268869684997973208337)
                ·
                  refine ⟨20137701652263748479906253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26850268869684997973208337 20137701652263748479906253)
                  ·
                    refine ⟨7551638119598905679964845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20137701652263748479906253 7551638119598905679964845)
                    ·
                      refine ⟨2831864294849589629986817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7551638119598905679964845 2831864294849589629986817)
                      ·
                        rfl

theorem cell23_5515036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_5515036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515036 prefixEnd_5515036 := by exact prefixLift 5515036
  have htrace : WordTrace (prefixWord ++ tailWord_5515036) baseStart_5515036 baseEnd_5515036 := by
    simpa [prefixWord, tailWord_5515036, baseEnd_5515036] using wordTrace_append hprefix tailTrace_5515036
  have hstable : (prefixWord ++ tailWord_5515036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515036).length < 2 ^ (prefixWord ++ tailWord_5515036).sum := by decide
  have hdescent : baseEnd_5515036 < baseStart_5515036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515043 : List Nat := [1, 1, 1, 4, 2, 1, 6, 2, 5]
def baseStart_5515043 : Nat := 118140960795 + 5515043 * 2 ^ 59
def prefixEnd_5515043 : Nat := 4983230072969 + 3 ^ 40 * 5515043 * 2
def baseEnd_5515043 : Nat := 314651987690463455844365

theorem tailTrace_5515043 : CollatzResearch.WordTrace tailWord_5515043 prefixEnd_5515043 314651987690463455844365 := by
  unfold tailWord_5515043
  simp only [CollatzResearch.WordTrace]
  refine ⟨201150143358948580201469783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134100095572632386800979855 201150143358948580201469783)
  ·
    refine ⟨301725215038422870302204675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201150143358948580201469783 301725215038422870302204675)
    ·
      refine ⟨452587822557634305453307013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301725215038422870302204675 452587822557634305453307013)
      ·
        refine ⟨84860216729556432272495065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 452587822557634305453307013 84860216729556432272495065)
        ·
          refine ⟨63645162547167324204371299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84860216729556432272495065 63645162547167324204371299)
          ·
            refine ⟨95467743820750986306556949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63645162547167324204371299 95467743820750986306556949)
            ·
              refine ⟨4475050491597702483119857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95467743820750986306556949 4475050491597702483119857)
              ·
                refine ⟨3356287868698276862339893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475050491597702483119857 3356287868698276862339893)
                ·
                  refine ⟨314651987690463455844365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356287868698276862339893 314651987690463455844365)
                  ·
                    rfl

theorem cell23_5515043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 5].length) (baseStart_5515043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515043 prefixEnd_5515043 := by exact prefixLift 5515043
  have htrace : WordTrace (prefixWord ++ tailWord_5515043) baseStart_5515043 baseEnd_5515043 := by
    simpa [prefixWord, tailWord_5515043, baseEnd_5515043] using wordTrace_append hprefix tailTrace_5515043
  have hstable : (prefixWord ++ tailWord_5515043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515043).length < 2 ^ (prefixWord ++ tailWord_5515043).sum := by decide
  have hdescent : baseEnd_5515043 < baseStart_5515043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515093 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_5515093 : Nat := 118140960795 + 5515093 * 2 ^ 59
def prefixEnd_5515093 : Nat := 4983230072969 + 3 ^ 40 * 5515093 * 2
def baseEnd_5515093 : Nat := 2831893563246895906974055

theorem tailTrace_5515093 : CollatzResearch.WordTrace tailWord_5515093 prefixEnd_5515093 2831893563246895906974055 := by
  unfold tailWord_5515093
  simp only [CollatzResearch.WordTrace]
  refine ⟨201151967008767438740789933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134101311339178292493859955 201151967008767438740789933)
  ·
    refine ⟨75431987628287789527796225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201151967008767438740789933 75431987628287789527796225)
    ·
      refine ⟨56573990721215842145847169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75431987628287789527796225 56573990721215842145847169)
      ·
        refine ⟨42430493040911881609385377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56573990721215842145847169 42430493040911881609385377)
        ·
          refine ⟨31822869780683911207039033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42430493040911881609385377 31822869780683911207039033)
          ·
            refine ⟨23867152335512933405279275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31822869780683911207039033 23867152335512933405279275)
            ·
              refine ⟨35800728503269400107918913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23867152335512933405279275 35800728503269400107918913)
              ·
                refine ⟨26850546377452050080939185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35800728503269400107918913 26850546377452050080939185)
                ·
                  refine ⟨20137909783089037560704389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26850546377452050080939185 20137909783089037560704389)
                  ·
                    refine ⟨3775858084329194542632073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20137909783089037560704389 3775858084329194542632073)
                    ·
                      refine ⟨2831893563246895906974055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775858084329194542632073 2831893563246895906974055)
                      ·
                        rfl

theorem cell23_5515093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_5515093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515093 prefixEnd_5515093 := by exact prefixLift 5515093
  have htrace : WordTrace (prefixWord ++ tailWord_5515093) baseStart_5515093 baseEnd_5515093 := by
    simpa [prefixWord, tailWord_5515093, baseEnd_5515093] using wordTrace_append hprefix tailTrace_5515093
  have hstable : (prefixWord ++ tailWord_5515093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515093).length < 2 ^ (prefixWord ++ tailWord_5515093).sum := by decide
  have hdescent : baseEnd_5515093 < baseStart_5515093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515103 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 3, 4]
def baseStart_5515103 : Nat := 118140960795 + 5515103 * 2 ^ 59
def prefixEnd_5515103 : Nat := 4983230072969 + 3 ^ 40 * 5515103 * 2
def baseEnd_5515103 : Nat := 943966232684480289283003

theorem tailTrace_5515103 : CollatzResearch.WordTrace tailWord_5515103 prefixEnd_5515103 943966232684480289283003 := by
  unfold tailWord_5515103
  simp only [CollatzResearch.WordTrace]
  refine ⟨201152331738731210448653963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134101554492487473632435975 201152331738731210448653963)
  ·
    refine ⟨301728497608096815672980945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201152331738731210448653963 301728497608096815672980945)
    ·
      refine ⟨226296373206072611754735709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301728497608096815672980945 226296373206072611754735709)
      ·
        refine ⟨84861139952277229408025891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226296373206072611754735709 84861139952277229408025891)
        ·
          refine ⟨127291709928415844112038837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84861139952277229408025891 127291709928415844112038837)
          ·
            refine ⟨11933597805788985385503641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127291709928415844112038837 11933597805788985385503641)
            ·
              refine ⟨8950198354341739039127731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11933597805788985385503641 8950198354341739039127731)
              ·
                refine ⟨13425297531512608558691597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8950198354341739039127731 13425297531512608558691597)
                ·
                  refine ⟨5034486574317228209509349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13425297531512608558691597 5034486574317228209509349)
                  ·
                    refine ⟨943966232684480289283003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5034486574317228209509349 943966232684480289283003)
                    ·
                      rfl

theorem cell23_5515103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 4].length) (baseStart_5515103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515103 prefixEnd_5515103 := by exact prefixLift 5515103
  have htrace : WordTrace (prefixWord ++ tailWord_5515103) baseStart_5515103 baseEnd_5515103 := by
    simpa [prefixWord, tailWord_5515103, baseEnd_5515103] using wordTrace_append hprefix tailTrace_5515103
  have hstable : (prefixWord ++ tailWord_5515103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515103).length < 2 ^ (prefixWord ++ tailWord_5515103).sum := by decide
  have hdescent : baseEnd_5515103 < baseStart_5515103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515153 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 4, 3, 2]
def baseStart_5515153 : Nat := 118140960795 + 5515153 * 2 ^ 59
def prefixEnd_5515153 : Nat := 4983230072969 + 3 ^ 40 * 5515153 * 2
def baseEnd_5515153 : Nat := 2831924372086165672223779

theorem tailTrace_5515153 : CollatzResearch.WordTrace tailWord_5515153 prefixEnd_5515153 2831924372086165672223779 := by
  unfold tailWord_5515153
  simp only [CollatzResearch.WordTrace]
  refine ⟨201154155388550068987974113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134102770259033379325316075 201154155388550068987974113)
  ·
    refine ⟨150865616541412551740980585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201154155388550068987974113 150865616541412551740980585)
    ·
      refine ⟨113149212406059413805735439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150865616541412551740980585 113149212406059413805735439)
      ·
        refine ⟨169723818609089120708603159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113149212406059413805735439 169723818609089120708603159)
        ·
          refine ⟨254585727913633681062904739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169723818609089120708603159 254585727913633681062904739)
          ·
            refine ⟨381878591870450521594357109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254585727913633681062904739 381878591870450521594357109)
            ·
              refine ⟨35801117987854736399470979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381878591870450521594357109 35801117987854736399470979)
              ·
                refine ⟨53701676981782104599206469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35801117987854736399470979 53701676981782104599206469)
                ·
                  refine ⟨10069064434084144612351213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53701676981782104599206469 10069064434084144612351213)
                  ·
                    refine ⟨3775899162781554229631705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10069064434084144612351213 3775899162781554229631705)
                    ·
                      refine ⟨2831924372086165672223779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775899162781554229631705 2831924372086165672223779)
                      ·
                        rfl

theorem cell23_5515153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_5515153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515153 prefixEnd_5515153 := by exact prefixLift 5515153
  have htrace : WordTrace (prefixWord ++ tailWord_5515153) baseStart_5515153 baseEnd_5515153 := by
    simpa [prefixWord, tailWord_5515153, baseEnd_5515153] using wordTrace_append hprefix tailTrace_5515153
  have hstable : (prefixWord ++ tailWord_5515153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515153).length < 2 ^ (prefixWord ++ tailWord_5515153).sum := by decide
  have hdescent : baseEnd_5515153 < baseStart_5515153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515154 : List Nat := [3, 2, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_5515154 : Nat := 118140960795 + 5515154 * 2 ^ 59
def prefixEnd_5515154 : Nat := 4983230072969 + 3 ^ 40 * 5515154 * 2
def baseEnd_5515154 : Nat := 943974961855606722770425

theorem tailTrace_5515154 : CollatzResearch.WordTrace tailWord_5515154 prefixEnd_5515154 943974961855606722770425 := by
  unfold tailWord_5515154
  simp only [CollatzResearch.WordTrace]
  refine ⟨50288547965386611539690129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134102794574364297439173677 50288547965386611539690129)
  ·
    refine ⟨37716410974039958654767597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50288547965386611539690129 37716410974039958654767597)
    ·
      refine ⟨14143654115264984495537849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37716410974039958654767597 14143654115264984495537849)
      ·
        refine ⟨10607740586448738371653387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14143654115264984495537849 10607740586448738371653387)
        ·
          refine ⟨15911610879673107557480081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10607740586448738371653387 15911610879673107557480081)
          ·
            refine ⟨11933708159754830668110061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15911610879673107557480081 11933708159754830668110061)
            ·
              refine ⟨4475140559908061500541273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11933708159754830668110061 4475140559908061500541273)
              ·
                refine ⟨3356355419931046125405955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475140559908061500541273 3356355419931046125405955)
                ·
                  refine ⟨5034533129896569188108933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356355419931046125405955 5034533129896569188108933)
                  ·
                    refine ⟨943974961855606722770425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5034533129896569188108933 943974961855606722770425)
                    ·
                      rfl

theorem cell23_5515154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_5515154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515154 prefixEnd_5515154 := by exact prefixLift 5515154
  have htrace : WordTrace (prefixWord ++ tailWord_5515154) baseStart_5515154 baseEnd_5515154 := by
    simpa [prefixWord, tailWord_5515154, baseEnd_5515154] using wordTrace_append hprefix tailTrace_5515154
  have hstable : (prefixWord ++ tailWord_5515154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515154).length < 2 ^ (prefixWord ++ tailWord_5515154).sum := by decide
  have hdescent : baseEnd_5515154 < baseStart_5515154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515167 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 6]
def baseStart_5515167 : Nat := 118140960795 + 5515167 * 2 ^ 59
def prefixEnd_5515167 : Nat := 4983230072969 + 3 ^ 40 * 5515167 * 2
def baseEnd_5515167 : Nat := 314659062312814290827635

theorem tailTrace_5515167 : CollatzResearch.WordTrace tailWord_5515167 prefixEnd_5515167 314659062312814290827635 := by
  unfold tailWord_5515167
  simp only [CollatzResearch.WordTrace]
  refine ⟨201154666010499349378983755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134103110673666232919322503 201154666010499349378983755)
  ·
    refine ⟨301731999015749024068475633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201154666010499349378983755 301731999015749024068475633)
    ·
      refine ⟨226298999261811768051356725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301731999015749024068475633 226298999261811768051356725)
      ·
        refine ⟨21215531180794853254814693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226298999261811768051356725 21215531180794853254814693)
        ·
          refine ⟨3977912096399034985277755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21215531180794853254814693 3977912096399034985277755)
          ·
            refine ⟨5966868144598552477916633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977912096399034985277755 5966868144598552477916633)
            ·
              refine ⟨4475151108448914358437475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5966868144598552477916633 4475151108448914358437475)
              ·
                refine ⟨6712726662673371537656213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475151108448914358437475 6712726662673371537656213)
                ·
                  refine ⟨314659062312814290827635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6712726662673371537656213 314659062312814290827635)
                  ·
                    rfl

theorem cell23_5515167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 6].length) (baseStart_5515167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515167 prefixEnd_5515167 := by exact prefixLift 5515167
  have htrace : WordTrace (prefixWord ++ tailWord_5515167) baseStart_5515167 baseEnd_5515167 := by
    simpa [prefixWord, tailWord_5515167, baseEnd_5515167] using wordTrace_append hprefix tailTrace_5515167
  have hstable : (prefixWord ++ tailWord_5515167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515167).length < 2 ^ (prefixWord ++ tailWord_5515167).sum := by decide
  have hdescent : baseEnd_5515167 < baseStart_5515167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515186 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_5515186 : Nat := 118140960795 + 5515186 * 2 ^ 59
def prefixEnd_5515186 : Nat := 4983230072969 + 3 ^ 40 * 5515186 * 2
def baseEnd_5515186 : Nat := 2831941316947764043111127

theorem tailTrace_5515186 : CollatzResearch.WordTrace tailWord_5515186 prefixEnd_5515186 2831941316947764043111127 := by
  unfold tailWord_5515186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50288839749357628905981353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134103572664953677082616941 50288839749357628905981353)
  ·
    refine ⟨37716629812018221679486015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50288839749357628905981353 37716629812018221679486015)
    ·
      refine ⟨56574944718027332519229023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37716629812018221679486015 56574944718027332519229023)
      ·
        refine ⟨84862417077040998778843535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56574944718027332519229023 84862417077040998778843535)
        ·
          refine ⟨127293625615561498168265303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84862417077040998778843535 127293625615561498168265303)
          ·
            refine ⟨190940438423342247252397955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127293625615561498168265303 190940438423342247252397955)
            ·
              refine ⟨286410657635013370878596933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190940438423342247252397955 286410657635013370878596933)
              ·
                refine ⟨53701998306565007039736925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286410657635013370878596933 53701998306565007039736925)
                ·
                  refine ⟨20138249364961877639901347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53701998306565007039736925 20138249364961877639901347)
                  ·
                    refine ⟨30207374047442816459852021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20138249364961877639901347 30207374047442816459852021)
                    ·
                      refine ⟨2831941316947764043111127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30207374047442816459852021 2831941316947764043111127)
                      ·
                        rfl

theorem cell23_5515186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_5515186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515186 prefixEnd_5515186 := by exact prefixLift 5515186
  have htrace : WordTrace (prefixWord ++ tailWord_5515186) baseStart_5515186 baseEnd_5515186 := by
    simpa [prefixWord, tailWord_5515186, baseEnd_5515186] using wordTrace_append hprefix tailTrace_5515186
  have hstable : (prefixWord ++ tailWord_5515186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515186).length < 2 ^ (prefixWord ++ tailWord_5515186).sum := by decide
  have hdescent : baseEnd_5515186 < baseStart_5515186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515200 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 1, 1, 4]
def baseStart_5515200 : Nat := 118140960795 + 5515200 * 2 ^ 59
def prefixEnd_5515200 : Nat := 4983230072969 + 3 ^ 40 * 5515200 * 2
def baseEnd_5515200 : Nat := 2831948505676926988336063

theorem tailTrace_5515200 : CollatzResearch.WordTrace tailWord_5515200 prefixEnd_5515200 2831948505676926988336063 := by
  unfold tailWord_5515200
  simp only [CollatzResearch.WordTrace]
  refine ⟨100577934809689898007467527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134103913079586530676623369 100577934809689898007467527)
  ·
    refine ⟨150866902214534847011201291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100577934809689898007467527 150866902214534847011201291)
    ·
      refine ⟨226300353321802270516801937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150866902214534847011201291 226300353321802270516801937)
      ·
        refine ⟨169725264991351702887601453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226300353321802270516801937 169725264991351702887601453)
        ·
          refine ⟨63646974371756888582850545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169725264991351702887601453 63646974371756888582850545)
          ·
            refine ⟨47735230778817666437137909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63646974371756888582850545 47735230778817666437137909)
            ·
              refine ⟨4475177885514156228481679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47735230778817666437137909 4475177885514156228481679)
              ·
                refine ⟨6712766828271234342722519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475177885514156228481679 6712766828271234342722519)
                ·
                  refine ⟨10069150242406851514083779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6712766828271234342722519 10069150242406851514083779)
                  ·
                    refine ⟨15103725363610277271125669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10069150242406851514083779 15103725363610277271125669)
                    ·
                      refine ⟨2831948505676926988336063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15103725363610277271125669 2831948505676926988336063)
                      ·
                        rfl

theorem cell23_5515200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_5515200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515200 prefixEnd_5515200 := by exact prefixLift 5515200
  have htrace : WordTrace (prefixWord ++ tailWord_5515200) baseStart_5515200 baseEnd_5515200 := by
    simpa [prefixWord, tailWord_5515200, baseEnd_5515200] using wordTrace_append hprefix tailTrace_5515200
  have hstable : (prefixWord ++ tailWord_5515200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515200).length < 2 ^ (prefixWord ++ tailWord_5515200).sum := by decide
  have hdescent : baseEnd_5515200 < baseStart_5515200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515233 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_5515233 : Nat := 118140960795 + 5515233 * 2 ^ 59
def prefixEnd_5515233 : Nat := 4983230072969 + 3 ^ 40 * 5515233 * 2
def baseEnd_5515233 : Nat := 2831965450538525359223411

theorem tailTrace_5515233 : CollatzResearch.WordTrace tailWord_5515233 prefixEnd_5515233 2831965450538525359223411 := by
  unfold tailWord_5515233
  simp only [CollatzResearch.WordTrace]
  refine ⟨201157073228260242650886353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134104715485506828433924235 201157073228260242650886353)
  ·
    refine ⟨150867804921195181988164765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201157073228260242650886353 150867804921195181988164765)
    ·
      refine ⟨56575426845448193245561787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150867804921195181988164765 56575426845448193245561787)
      ·
        refine ⟨84863140268172289868342681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56575426845448193245561787 84863140268172289868342681)
        ·
          refine ⟨63647355201129217401257011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84863140268172289868342681 63647355201129217401257011)
          ·
            refine ⟨95471032801693826101885517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63647355201129217401257011 95471032801693826101885517)
            ·
              refine ⟨35801637300635184788207069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95471032801693826101885517 35801637300635184788207069)
              ·
                refine ⟨13425613987738194295577651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35801637300635184788207069 13425613987738194295577651)
                ·
                  refine ⟨20138420981607291443366477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13425613987738194295577651 20138420981607291443366477)
                  ·
                    refine ⟨7551907868102734291262429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20138420981607291443366477 7551907868102734291262429)
                    ·
                      refine ⟨2831965450538525359223411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7551907868102734291262429 2831965450538525359223411)
                      ·
                        rfl

theorem cell23_5515233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_5515233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515233 prefixEnd_5515233 := by exact prefixLift 5515233
  have htrace : WordTrace (prefixWord ++ tailWord_5515233) baseStart_5515233 baseEnd_5515233 := by
    simpa [prefixWord, tailWord_5515233, baseEnd_5515233] using wordTrace_append hprefix tailTrace_5515233
  have hstable : (prefixWord ++ tailWord_5515233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515233).length < 2 ^ (prefixWord ++ tailWord_5515233).sum := by decide
  have hdescent : baseEnd_5515233 < baseStart_5515233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515236 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_5515236 : Nat := 118140960795 + 5515236 * 2 ^ 59
def prefixEnd_5515236 : Nat := 4983230072969 + 3 ^ 40 * 5515236 * 2
def baseEnd_5515236 : Nat := 943988996993496282495299

theorem tailTrace_5515236 : CollatzResearch.WordTrace tailWord_5515236 prefixEnd_5515236 943988996993496282495299 := by
  unfold tailWord_5515236
  simp only [CollatzResearch.WordTrace]
  refine ⟨100578591323624687081622781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134104788431499582775497041 100578591323624687081622781)
  ·
    refine ⟨37716971746359257655608543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100578591323624687081622781 37716971746359257655608543)
    ·
      refine ⟨56575457619538886483412815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37716971746359257655608543 56575457619538886483412815)
      ·
        refine ⟨84863186429308329725119223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56575457619538886483412815 84863186429308329725119223)
        ·
          refine ⟨127294779643962494587678835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84863186429308329725119223 127294779643962494587678835)
          ·
            refine ⟨190942169465943741881518253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127294779643962494587678835 190942169465943741881518253)
            ·
              refine ⟨71603313549728903205569345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190942169465943741881518253 71603313549728903205569345)
              ·
                refine ⟨53702485162296677404177009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71603313549728903205569345 53702485162296677404177009)
                ·
                  refine ⟨40276863871722508053132757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53702485162296677404177009 40276863871722508053132757)
                  ·
                    refine ⟨943988996993496282495299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40276863871722508053132757 943988996993496282495299)
                    ·
                      rfl

theorem cell23_5515236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_5515236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515236 prefixEnd_5515236 := by exact prefixLift 5515236
  have htrace : WordTrace (prefixWord ++ tailWord_5515236) baseStart_5515236 baseEnd_5515236 := by
    simpa [prefixWord, tailWord_5515236, baseEnd_5515236] using wordTrace_append hprefix tailTrace_5515236
  have hstable : (prefixWord ++ tailWord_5515236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515236).length < 2 ^ (prefixWord ++ tailWord_5515236).sum := by decide
  have hdescent : baseEnd_5515236 < baseStart_5515236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515273 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 8, 2]
def baseStart_5515273 : Nat := 118140960795 + 5515273 * 2 ^ 59
def prefixEnd_5515273 : Nat := 4983230072969 + 3 ^ 40 * 5515273 * 2
def baseEnd_5515273 : Nat := 2831985989764705202723227

theorem tailTrace_5515273 : CollatzResearch.WordTrace tailWord_5515273 prefixEnd_5515273 2831985989764705202723227 := by
  unfold tailWord_5515273
  simp only [CollatzResearch.WordTrace]
  refine ⟨201158532148115329482342473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134105688098743552988228315 201158532148115329482342473)
  ·
    refine ⟨150868899111086497111756855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201158532148115329482342473 150868899111086497111756855)
    ·
      refine ⟨226303348666629745667635283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150868899111086497111756855 226303348666629745667635283)
      ·
        refine ⟨339455022999944618501452925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226303348666629745667635283 339455022999944618501452925)
        ·
          refine ⟨127295633624979231938044847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339455022999944618501452925 127295633624979231938044847)
          ·
            refine ⟨190943450437468847907067271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127295633624979231938044847 190943450437468847907067271)
            ·
              refine ⟨286415175656203271860600907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190943450437468847907067271 286415175656203271860600907)
              ·
                refine ⟨429622763484304907790901361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286415175656203271860600907 429622763484304907790901361)
                ·
                  refine ⟨322217072613228680843176021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429622763484304907790901361 322217072613228680843176021)
                  ·
                    refine ⟨3775981319686273603630969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 322217072613228680843176021 3775981319686273603630969)
                    ·
                      refine ⟨2831985989764705202723227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3775981319686273603630969 2831985989764705202723227)
                      ·
                        rfl

theorem cell23_5515273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 8, 2].length) (baseStart_5515273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515273 prefixEnd_5515273 := by exact prefixLift 5515273
  have htrace : WordTrace (prefixWord ++ tailWord_5515273) baseStart_5515273 baseEnd_5515273 := by
    simpa [prefixWord, tailWord_5515273, baseEnd_5515273] using wordTrace_append hprefix tailTrace_5515273
  have hstable : (prefixWord ++ tailWord_5515273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515273).length < 2 ^ (prefixWord ++ tailWord_5515273).sum := by decide
  have hdescent : baseEnd_5515273 < baseStart_5515273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515310 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5515310 : Nat := 118140960795 + 5515310 * 2 ^ 59
def prefixEnd_5515310 : Nat := 4983230072969 + 3 ^ 40 * 5515310 * 2
def baseEnd_5515310 : Nat := 2832004988548921557960557

theorem tailTrace_5515310 : CollatzResearch.WordTrace tailWord_5515310 prefixEnd_5515310 2832004988548921557960557 := by
  unfold tailWord_5515310
  simp only [CollatzResearch.WordTrace]
  refine ⟨25144985206122660600179923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134106587765987523200959589 25144985206122660600179923)
  ·
    refine ⟨37717477809183990900269885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25144985206122660600179923 37717477809183990900269885)
    ·
      refine ⟨14144054178443996587601207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37717477809183990900269885 14144054178443996587601207)
      ·
        refine ⟨21216081267665994881401811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14144054178443996587601207 21216081267665994881401811)
        ·
          refine ⟨31824121901498992322102717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21216081267665994881401811 31824121901498992322102717)
          ·
            refine ⟨11934045713062122120788519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31824121901498992322102717 11934045713062122120788519)
            ·
              refine ⟨17901068569593183181182779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11934045713062122120788519 17901068569593183181182779)
              ·
                refine ⟨26851602854389774771774169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17901068569593183181182779 26851602854389774771774169)
                ·
                  refine ⟨20138702140792331078830627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26851602854389774771774169 20138702140792331078830627)
                  ·
                    refine ⟨30208053211188496618245941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20138702140792331078830627 30208053211188496618245941)
                    ·
                      refine ⟨2832004988548921557960557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30208053211188496618245941 2832004988548921557960557)
                      ·
                        rfl

theorem cell23_5515310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5515310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515310 prefixEnd_5515310 := by exact prefixLift 5515310
  have htrace : WordTrace (prefixWord ++ tailWord_5515310) baseStart_5515310 baseEnd_5515310 := by
    simpa [prefixWord, tailWord_5515310, baseEnd_5515310] using wordTrace_append hprefix tailTrace_5515310
  have hstable : (prefixWord ++ tailWord_5515310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515310).length < 2 ^ (prefixWord ++ tailWord_5515310).sum := by decide
  have hdescent : baseEnd_5515310 < baseStart_5515310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515360 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 2, 5]
def baseStart_5515360 : Nat := 118140960795 + 5515360 * 2 ^ 59
def prefixEnd_5515360 : Nat := 4983230072969 + 3 ^ 40 * 5515360 * 2
def baseEnd_5515360 : Nat := 944010220860548787445109

theorem tailTrace_5515360 : CollatzResearch.WordTrace tailWord_5515360 prefixEnd_5515360 944010220860548787445109 := by
  unfold tailWord_5515360
  simp only [CollatzResearch.WordTrace]
  refine ⟨100580852649400071670379767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134107803532533428893839689 100580852649400071670379767)
  ·
    refine ⟨150871278974100107505569651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100580852649400071670379767 150871278974100107505569651)
    ·
      refine ⟨226306918461150161258354477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150871278974100107505569651 226306918461150161258354477)
      ·
        refine ⟨84865094422931310471882929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226306918461150161258354477 84865094422931310471882929)
        ·
          refine ⟨63648820817198482853912197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84865094422931310471882929 63648820817198482853912197)
          ·
            refine ⟨11934153903224715535108537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63648820817198482853912197 11934153903224715535108537)
            ·
              refine ⟨8950615427418536651331403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11934153903224715535108537 8950615427418536651331403)
              ·
                refine ⟨13425923141127804976997105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8950615427418536651331403 13425923141127804976997105)
                ·
                  refine ⟨10069442355845853732747829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13425923141127804976997105 10069442355845853732747829)
                  ·
                    refine ⟨944010220860548787445109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10069442355845853732747829 944010220860548787445109)
                    ·
                      rfl

theorem cell23_5515360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_5515360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515360 prefixEnd_5515360 := by exact prefixLift 5515360
  have htrace : WordTrace (prefixWord ++ tailWord_5515360) baseStart_5515360 baseEnd_5515360 := by
    simpa [prefixWord, tailWord_5515360, baseEnd_5515360] using wordTrace_append hprefix tailTrace_5515360
  have hstable : (prefixWord ++ tailWord_5515360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515360).length < 2 ^ (prefixWord ++ tailWord_5515360).sum := by decide
  have hdescent : baseEnd_5515360 < baseStart_5515360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515363 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 4]
def baseStart_5515363 : Nat := 118140960795 + 5515363 * 2 ^ 59
def prefixEnd_5515363 : Nat := 4983230072969 + 3 ^ 40 * 5515363 * 2
def baseEnd_5515363 : Nat := 2832032203023609850597813

theorem tailTrace_5515363 : CollatzResearch.WordTrace tailWord_5515363 prefixEnd_5515363 2832032203023609850597813 := by
  unfold tailWord_5515363
  simp only [CollatzResearch.WordTrace]
  refine ⟨201161814717789274853118743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134107876478526183235412495 201161814717789274853118743)
  ·
    refine ⟨301742722076683912279678115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201161814717789274853118743 301742722076683912279678115)
    ·
      refine ⟨452614083115025868419517173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301742722076683912279678115 452614083115025868419517173)
      ·
        refine ⟨42432570292033675164329735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 452614083115025868419517173 42432570292033675164329735)
        ·
          refine ⟨63648855438050512746494603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42432570292033675164329735 63648855438050512746494603)
          ·
            refine ⟨95473283157075769119741905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63648855438050512746494603 95473283157075769119741905)
            ·
              refine ⟨71604962367806826839806429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95473283157075769119741905 71604962367806826839806429)
              ·
                refine ⟨26851860887927560064927411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71604962367806826839806429 26851860887927560064927411)
                ·
                  refine ⟨40277791331891340097391117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26851860887927560064927411 40277791331891340097391117)
                  ·
                    refine ⟨15104171749459252536521669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40277791331891340097391117 15104171749459252536521669)
                    ·
                      refine ⟨2832032203023609850597813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15104171749459252536521669 2832032203023609850597813)
                      ·
                        rfl

theorem cell23_5515363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_5515363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515363 prefixEnd_5515363 := by exact prefixLift 5515363
  have htrace : WordTrace (prefixWord ++ tailWord_5515363) baseStart_5515363 baseEnd_5515363 := by
    simpa [prefixWord, tailWord_5515363, baseEnd_5515363] using wordTrace_append hprefix tailTrace_5515363
  have hstable : (prefixWord ++ tailWord_5515363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515363).length < 2 ^ (prefixWord ++ tailWord_5515363).sum := by decide
  have hdescent : baseEnd_5515363 < baseStart_5515363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515397 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 2, 4, 2]
def baseStart_5515397 : Nat := 118140960795 + 5515397 * 2 ^ 59
def prefixEnd_5515397 : Nat := 4983230072969 + 3 ^ 40 * 5515397 * 2
def baseEnd_5515397 : Nat := 2832049661365862717572657

theorem tailTrace_5515397 : CollatzResearch.WordTrace tailWord_5515397 prefixEnd_5515397 2832049661365862717572657 := by
  unfold tailWord_5515397
  simp only [CollatzResearch.WordTrace]
  refine ⟨201163054799666098659856445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134108703199777399106570963 201163054799666098659856445)
  ·
    refine ⟨75436145549874786997446167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201163054799666098659856445 75436145549874786997446167)
    ·
      refine ⟨113154218324812180496169251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75436145549874786997446167 113154218324812180496169251)
      ·
        refine ⟨169731327487218270744253877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113154218324812180496169251 169731327487218270744253877)
        ·
          refine ⟨15912311951926712882273801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169731327487218270744253877 15912311951926712882273801)
          ·
            refine ⟨11934233963945034661705351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15912311951926712882273801 11934233963945034661705351)
            ·
              refine ⟨17901350945917551992558027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11934233963945034661705351 17901350945917551992558027)
              ·
                refine ⟨26852026418876327988837041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17901350945917551992558027 26852026418876327988837041)
                ·
                  refine ⟨20139019814157245991627781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26852026418876327988837041 20139019814157245991627781)
                  ·
                    refine ⟨3776066215154483623430209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20139019814157245991627781 3776066215154483623430209)
                    ·
                      refine ⟨2832049661365862717572657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776066215154483623430209 2832049661365862717572657)
                      ·
                        rfl

theorem cell23_5515397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_5515397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515397 prefixEnd_5515397 := by exact prefixLift 5515397
  have htrace : WordTrace (prefixWord ++ tailWord_5515397) baseStart_5515397 baseEnd_5515397 := by
    simpa [prefixWord, tailWord_5515397, baseEnd_5515397] using wordTrace_append hprefix tailTrace_5515397
  have hstable : (prefixWord ++ tailWord_5515397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515397).length < 2 ^ (prefixWord ++ tailWord_5515397).sum := by decide
  have hdescent : baseEnd_5515397 < baseStart_5515397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515424 : List Nat := [2, 1, 1, 4, 2, 3, 2, 3, 1, 4]
def baseStart_5515424 : Nat := 118140960795 + 5515424 * 2 ^ 59
def prefixEnd_5515424 : Nat := 4983230072969 + 3 ^ 40 * 5515424 * 2
def baseEnd_5515424 : Nat := 944021175114511370645011

theorem tailTrace_5515424 : CollatzResearch.WordTrace tailWord_5515424 prefixEnd_5515424 944021175114511370645011 := by
  unfold tailWord_5515424
  simp only [CollatzResearch.WordTrace]
  refine ⟨100582019785284141135544663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134109359713712188180726217 100582019785284141135544663)
  ·
    refine ⟨150873029677926211703316995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100582019785284141135544663 150873029677926211703316995)
    ·
      refine ⟨226309544516889317554975493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150873029677926211703316995 226309544516889317554975493)
      ·
        refine ⟨42433039596916747041557905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226309544516889317554975493 42433039596916747041557905)
        ·
          refine ⟨31824779697687560281168429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42433039596916747041557905 31824779697687560281168429)
          ·
            refine ⟨11934292386632835105438161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31824779697687560281168429 11934292386632835105438161)
            ·
              refine ⟨8950719289974626329078621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11934292386632835105438161 8950719289974626329078621)
              ·
                refine ⟨3356519733740484873404483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8950719289974626329078621 3356519733740484873404483)
                ·
                  refine ⟨5034779600610727310106725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356519733740484873404483 5034779600610727310106725)
                  ·
                    refine ⟨944021175114511370645011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5034779600610727310106725 944021175114511370645011)
                    ·
                      rfl

theorem cell23_5515424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 4].length) (baseStart_5515424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515424 prefixEnd_5515424 := by exact prefixLift 5515424
  have htrace : WordTrace (prefixWord ++ tailWord_5515424) baseStart_5515424 baseEnd_5515424 := by
    simpa [prefixWord, tailWord_5515424, baseEnd_5515424] using wordTrace_append hprefix tailTrace_5515424
  have hstable : (prefixWord ++ tailWord_5515424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515424).length < 2 ^ (prefixWord ++ tailWord_5515424).sum := by decide
  have hdescent : baseEnd_5515424 < baseStart_5515424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515437 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 6]
def baseStart_5515437 : Nat := 118140960795 + 5515437 * 2 ^ 59
def prefixEnd_5515437 : Nat := 4983230072969 + 3 ^ 40 * 5515437 * 2
def baseEnd_5515437 : Nat := 314674466732449173452497

theorem tailTrace_5515437 : CollatzResearch.WordTrace tailWord_5515437 prefixEnd_5515437 314674466732449173452497 := by
  unfold tailWord_5515437
  simp only [CollatzResearch.WordTrace]
  refine ⟨201164513719521185491312565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134109675813014123660875043 201164513719521185491312565)
  ·
    refine ⟨18859173161205111139810553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201164513719521185491312565 18859173161205111139810553)
    ·
      refine ⟨14144379870903833354857915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18859173161205111139810553 14144379870903833354857915)
      ·
        refine ⟨21216569806355750032286873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14144379870903833354857915 21216569806355750032286873)
        ·
          refine ⟨15912427354766812524215155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21216569806355750032286873 15912427354766812524215155)
          ·
            refine ⟨23868641032150218786322733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15912427354766812524215155 23868641032150218786322733)
            ·
              refine ⟨8950740387056332044871025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23868641032150218786322733 8950740387056332044871025)
              ·
                refine ⟨6713055290292249033653269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8950740387056332044871025 6713055290292249033653269)
                ·
                  refine ⟨314674466732449173452497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6713055290292249033653269 314674466732449173452497)
                  ·
                    rfl

theorem cell23_5515437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_5515437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515437 prefixEnd_5515437 := by exact prefixLift 5515437
  have htrace : WordTrace (prefixWord ++ tailWord_5515437) baseStart_5515437 baseEnd_5515437 := by
    simpa [prefixWord, tailWord_5515437, baseEnd_5515437] using wordTrace_append hprefix tailTrace_5515437
  have hstable : (prefixWord ++ tailWord_5515437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515437).length < 2 ^ (prefixWord ++ tailWord_5515437).sum := by decide
  have hdescent : baseEnd_5515437 < baseStart_5515437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515440 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 5, 5, 2]
def baseStart_5515440 : Nat := 118140960795 + 5515440 * 2 ^ 59
def prefixEnd_5515440 : Nat := 4983230072969 + 3 ^ 40 * 5515440 * 2
def baseEnd_5515440 : Nat := 2832071741034006049334959

theorem tailTrace_5515440 : CollatzResearch.WordTrace tailWord_5515440 prefixEnd_5515440 2832071741034006049334959 := by
  unfold tailWord_5515440
  simp only [CollatzResearch.WordTrace]
  refine ⟨100582311569255158501835887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134109748759006878002447849 100582311569255158501835887)
  ·
    refine ⟨150873467353882737752753831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100582311569255158501835887 150873467353882737752753831)
    ·
      refine ⟨226310201030824106629130747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150873467353882737752753831 226310201030824106629130747)
      ·
        refine ⟨339465301546236159943696121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226310201030824106629130747 339465301546236159943696121)
        ·
          refine ⟨254598976159677119957772091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339465301546236159943696121 254598976159677119957772091)
          ·
            refine ⟨381898464239515679936658137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254598976159677119957772091 381898464239515679936658137)
            ·
              refine ⟨286423848179636759952493603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381898464239515679936658137 286423848179636759952493603)
              ·
                refine ⟨429635772269455139928740405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286423848179636759952493603 429635772269455139928740405)
                ·
                  refine ⟨40278353650261419368319413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 429635772269455139928740405 40278353650261419368319413)
                  ·
                    refine ⟨3776095654712008065779945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40278353650261419368319413 3776095654712008065779945)
                    ·
                      refine ⟨2832071741034006049334959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776095654712008065779945 2832071741034006049334959)
                      ·
                        rfl

theorem cell23_5515440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 5, 2].length) (baseStart_5515440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515440 prefixEnd_5515440 := by exact prefixLift 5515440
  have htrace : WordTrace (prefixWord ++ tailWord_5515440) baseStart_5515440 baseEnd_5515440 := by
    simpa [prefixWord, tailWord_5515440, baseEnd_5515440] using wordTrace_append hprefix tailTrace_5515440
  have hstable : (prefixWord ++ tailWord_5515440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515440).length < 2 ^ (prefixWord ++ tailWord_5515440).sum := by decide
  have hdescent : baseEnd_5515440 < baseStart_5515440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515447 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_5515447 : Nat := 118140960795 + 5515447 * 2 ^ 59
def prefixEnd_5515447 : Nat := 4983230072969 + 3 ^ 40 * 5515447 * 2
def baseEnd_5515447 : Nat := 2832075335398587521947427

theorem tailTrace_5515447 : CollatzResearch.WordTrace tailWord_5515447 prefixEnd_5515447 2832075335398587521947427 := by
  unfold tailWord_5515447
  simp only [CollatzResearch.WordTrace]
  refine ⟨201164878449484957199176595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134109918966323304799451063 201164878449484957199176595)
  ·
    refine ⟨301747317674227435798764893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201164878449484957199176595 301747317674227435798764893)
    ·
      refine ⟨113155244127835288424536835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301747317674227435798764893 113155244127835288424536835)
      ·
        refine ⟨169732866191752932636805253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113155244127835288424536835 169732866191752932636805253)
        ·
          refine ⟨31824912410953674869400985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169732866191752932636805253 31824912410953674869400985)
          ·
            refine ⟨23868684308215256152050739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31824912410953674869400985 23868684308215256152050739)
            ·
              refine ⟨35803026462322884228076109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23868684308215256152050739 35803026462322884228076109)
              ·
                refine ⟨13426134923371081585528541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35803026462322884228076109 13426134923371081585528541)
                ·
                  refine ⟨5034800596264155594573203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13426134923371081585528541 5034800596264155594573203)
                  ·
                    refine ⟨7552200894396233391859805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5034800596264155594573203 7552200894396233391859805)
                    ·
                      refine ⟨2832075335398587521947427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7552200894396233391859805 2832075335398587521947427)
                      ·
                        rfl

theorem cell23_5515447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_5515447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515447 prefixEnd_5515447 := by exact prefixLift 5515447
  have htrace : WordTrace (prefixWord ++ tailWord_5515447) baseStart_5515447 baseEnd_5515447 := by
    simpa [prefixWord, tailWord_5515447, baseEnd_5515447] using wordTrace_append hprefix tailTrace_5515447
  have hstable : (prefixWord ++ tailWord_5515447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515447).length < 2 ^ (prefixWord ++ tailWord_5515447).sum := by decide
  have hdescent : baseEnd_5515447 < baseStart_5515447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515454 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_5515454 : Nat := 118140960795 + 5515454 * 2 ^ 59
def prefixEnd_5515454 : Nat := 4983230072969 + 3 ^ 40 * 5515454 * 2
def baseEnd_5515454 : Nat := 314675436640352110506655

theorem tailTrace_5515454 : CollatzResearch.WordTrace tailWord_5515454 prefixEnd_5515454 314675436640352110506655 := by
  unfold tailWord_5515454
  simp only [CollatzResearch.WordTrace]
  refine ⟨25145641720057449674335177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134110089173639731596454277 25145641720057449674335177)
  ·
    refine ⟨18859231290043087255751383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25145641720057449674335177 18859231290043087255751383)
    ·
      refine ⟨28288846935064630883627075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18859231290043087255751383 28288846935064630883627075)
      ·
        refine ⟨42433270402596946325440613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28288846935064630883627075 42433270402596946325440613)
        ·
          refine ⟨7956238200486927436020115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42433270402596946325440613 7956238200486927436020115)
          ·
            refine ⟨11934357300730391154030173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956238200486927436020115 11934357300730391154030173)
            ·
              refine ⟨4475383987773896682761315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11934357300730391154030173 4475383987773896682761315)
              ·
                refine ⟨6713075981660845024141973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475383987773896682761315 6713075981660845024141973)
                ·
                  refine ⟨314675436640352110506655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6713075981660845024141973 314675436640352110506655)
                  ·
                    rfl

theorem cell23_5515454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_5515454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515454 prefixEnd_5515454 := by exact prefixLift 5515454
  have htrace : WordTrace (prefixWord ++ tailWord_5515454) baseStart_5515454 baseEnd_5515454 := by
    simpa [prefixWord, tailWord_5515454, baseEnd_5515454] using wordTrace_append hprefix tailTrace_5515454
  have hstable : (prefixWord ++ tailWord_5515454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515454).length < 2 ^ (prefixWord ++ tailWord_5515454).sum := by decide
  have hdescent : baseEnd_5515454 < baseStart_5515454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515483 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 6]
def baseStart_5515483 : Nat := 118140960795 + 5515483 * 2 ^ 59
def prefixEnd_5515483 : Nat := 4983230072969 + 3 ^ 40 * 5515483 * 2
def baseEnd_5515483 : Nat := 2832093820702149381097261

theorem tailTrace_5515483 : CollatzResearch.WordTrace tailWord_5515483 prefixEnd_5515483 2832093820702149381097261 := by
  unfold tailWord_5515483
  simp only [CollatzResearch.WordTrace]
  refine ⟨201166191477354535347487103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134110794318236356898324735 201166191477354535347487103)
  ·
    refine ⟨301749287216031803021230655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201166191477354535347487103 301749287216031803021230655)
    ·
      refine ⟨452623930824047704531845983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301749287216031803021230655 452623930824047704531845983)
      ·
        refine ⟨678935896236071556797768975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452623930824047704531845983 678935896236071556797768975)
        ·
          refine ⟨1018403844354107335196653463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678935896236071556797768975 1018403844354107335196653463)
          ·
            refine ⟨1527605766531161002794980195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018403844354107335196653463 1527605766531161002794980195)
            ·
              refine ⟨2291408649796741504192470293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527605766531161002794980195 2291408649796741504192470293)
              ·
                refine ⟨107409780459222258009022045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2291408649796741504192470293 107409780459222258009022045)
                ·
                  refine ⟨40278667672208346753383267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107409780459222258009022045 40278667672208346753383267)
                  ·
                    refine ⟨60418001508312520130074901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40278667672208346753383267 60418001508312520130074901)
                    ·
                      refine ⟨2832093820702149381097261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60418001508312520130074901 2832093820702149381097261)
                      ·
                        rfl

theorem cell23_5515483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_5515483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515483 prefixEnd_5515483 := by exact prefixLift 5515483
  have htrace : WordTrace (prefixWord ++ tailWord_5515483) baseStart_5515483 baseEnd_5515483 := by
    simpa [prefixWord, tailWord_5515483, baseEnd_5515483] using wordTrace_append hprefix tailTrace_5515483
  have hstable : (prefixWord ++ tailWord_5515483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515483).length < 2 ^ (prefixWord ++ tailWord_5515483).sum := by decide
  have hdescent : baseEnd_5515483 < baseStart_5515483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515491 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5515491 : Nat := 118140960795 + 5515491 * 2 ^ 59
def prefixEnd_5515491 : Nat := 4983230072969 + 3 ^ 40 * 5515491 * 2
def baseEnd_5515491 : Nat := 2832097928547385349797225

theorem tailTrace_5515491 : CollatzResearch.WordTrace tailWord_5515491 prefixEnd_5515491 2832097928547385349797225 := by
  unfold tailWord_5515491
  simp only [CollatzResearch.WordTrace]
  refine ⟨201166483261325552713778327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134110988840883701809185551 201166483261325552713778327)
  ·
    refine ⟨301749724891988329070667491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201166483261325552713778327 301749724891988329070667491)
    ·
      refine ⟨452624587337982493606001237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301749724891988329070667491 452624587337982493606001237)
      ·
        refine ⟨5304194382866982346945327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 452624587337982493606001237 5304194382866982346945327)
        ·
          refine ⟨7956291574300473520417991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304194382866982346945327 7956291574300473520417991)
          ·
            refine ⟨11934437361450710280626987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956291574300473520417991 11934437361450710280626987)
            ·
              refine ⟨17901656042176065420940481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11934437361450710280626987 17901656042176065420940481)
              ·
                refine ⟨13426242031632049065705361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17901656042176065420940481 13426242031632049065705361)
                ·
                  refine ⟨10069681523724036799279021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13426242031632049065705361 10069681523724036799279021)
                  ·
                    refine ⟨3776130571396513799729633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10069681523724036799279021 3776130571396513799729633)
                    ·
                      refine ⟨2832097928547385349797225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776130571396513799729633 2832097928547385349797225)
                      ·
                        rfl

theorem cell23_5515491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5515491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515491 prefixEnd_5515491 := by exact prefixLift 5515491
  have htrace : WordTrace (prefixWord ++ tailWord_5515491) baseStart_5515491 baseEnd_5515491 := by
    simpa [prefixWord, tailWord_5515491, baseEnd_5515491] using wordTrace_append hprefix tailTrace_5515491
  have hstable : (prefixWord ++ tailWord_5515491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515491).length < 2 ^ (prefixWord ++ tailWord_5515491).sum := by decide
  have hdescent : baseEnd_5515491 < baseStart_5515491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515510 : List Nat := [5, 1, 1, 1, 1, 1, 3, 10]
def baseStart_5515510 : Nat := 118140960795 + 5515510 * 2 ^ 59
def prefixEnd_5515510 : Nat := 4983230072969 + 3 ^ 40 * 5515510 * 2
def baseEnd_5515510 : Nat := 104892877210363732424431

theorem tailTrace_5515510 : CollatzResearch.WordTrace tailWord_5515510 prefixEnd_5515510 104892877210363732424431 := by
  unfold tailWord_5515510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12572948515516044934919999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134111450832171145972479989 12572948515516044934919999)
  ·
    refine ⟨18859422773274067402379999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12572948515516044934919999 18859422773274067402379999)
    ·
      refine ⟨28289134159911101103569999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18859422773274067402379999 28289134159911101103569999)
      ·
        refine ⟨42433701239866651655354999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28289134159911101103569999 42433701239866651655354999)
        ·
          refine ⟨63650551859799977483032499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42433701239866651655354999 63650551859799977483032499)
          ·
            refine ⟨95475827789699966224548749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63650551859799977483032499 95475827789699966224548749)
            ·
              refine ⟨35803435421137487334205781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95475827789699966224548749 35803435421137487334205781)
              ·
                refine ⟨104892877210363732424431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35803435421137487334205781 104892877210363732424431)
                ·
                  rfl

theorem cell23_5515510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_5515510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515510 prefixEnd_5515510 := by exact prefixLift 5515510
  have htrace : WordTrace (prefixWord ++ tailWord_5515510) baseStart_5515510 baseEnd_5515510 := by
    simpa [prefixWord, tailWord_5515510, baseEnd_5515510] using wordTrace_append hprefix tailTrace_5515510
  have hstable : (prefixWord ++ tailWord_5515510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515510).length < 2 ^ (prefixWord ++ tailWord_5515510).sum := by decide
  have hdescent : baseEnd_5515510 < baseStart_5515510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515514 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_5515514 : Nat := 118140960795 + 5515514 * 2 ^ 59
def prefixEnd_5515514 : Nat := 4983230072969 + 3 ^ 40 * 5515514 * 2
def baseEnd_5515514 : Nat := 944036579534146253269873

theorem tailTrace_5515514 : CollatzResearch.WordTrace tailWord_5515514 prefixEnd_5515514 944036579534146253269873 := by
  unfold tailWord_5515514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50291830535060556910466399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134111548093494818427910397 50291830535060556910466399)
  ·
    refine ⟨75437745802590835365699599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50291830535060556910466399 75437745802590835365699599)
    ·
      refine ⟨113156618703886253048549399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75437745802590835365699599 113156618703886253048549399)
      ·
        refine ⟨169734928055829379572824099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113156618703886253048549399 169734928055829379572824099)
        ·
          refine ⟨254602392083744069359236149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169734928055829379572824099 254602392083744069359236149)
          ·
            refine ⟨23868974257851006502428389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 254602392083744069359236149 23868974257851006502428389)
            ·
              refine ⟨4475432673347063719205323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23868974257851006502428389 4475432673347063719205323)
              ·
                refine ⟨6713149010020595578807985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475432673347063719205323 6713149010020595578807985)
                ·
                  refine ⟨5034861757515446684105989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6713149010020595578807985 5034861757515446684105989)
                  ·
                    refine ⟨944036579534146253269873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5034861757515446684105989 944036579534146253269873)
                    ·
                      rfl

theorem cell23_5515514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_5515514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515514 prefixEnd_5515514 := by exact prefixLift 5515514
  have htrace : WordTrace (prefixWord ++ tailWord_5515514) baseStart_5515514 baseEnd_5515514 := by
    simpa [prefixWord, tailWord_5515514, baseEnd_5515514] using wordTrace_append hprefix tailTrace_5515514
  have hstable : (prefixWord ++ tailWord_5515514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515514).length < 2 ^ (prefixWord ++ tailWord_5515514).sum := by decide
  have hdescent : baseEnd_5515514 < baseStart_5515514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515524 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_5515524 : Nat := 118140960795 + 5515524 * 2 ^ 59
def prefixEnd_5515524 : Nat := 4983230072969 + 3 ^ 40 * 5515524 * 2
def baseEnd_5515524 : Nat := 2832114873408983720684573

theorem tailTrace_5515524 : CollatzResearch.WordTrace tailWord_5515524 prefixEnd_5515524 2832114873408983720684573 := by
  unfold tailWord_5515524
  simp only [CollatzResearch.WordTrace]
  refine ⟨100583843435102999674864813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134111791246803999566486417 100583843435102999674864813)
  ·
    refine ⟨37718941288163624878074305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100583843435102999674864813 37718941288163624878074305)
    ·
      refine ⟨28289205966122718658555729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37718941288163624878074305 28289205966122718658555729)
      ·
        refine ⟨21216904474592038993916797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28289205966122718658555729 21216904474592038993916797)
        ·
          refine ⟨7956339177972014622718799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21216904474592038993916797 7956339177972014622718799)
          ·
            refine ⟨11934508766958021934078199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956339177972014622718799 11934508766958021934078199)
            ·
              refine ⟨17901763150437032901117299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11934508766958021934078199 17901763150437032901117299)
              ·
                refine ⟨26852644725655549351675949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17901763150437032901117299 26852644725655549351675949)
                ·
                  refine ⟨10069741772120831006878481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26852644725655549351675949 10069741772120831006878481)
                  ·
                    refine ⟨7552306329090623255158861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10069741772120831006878481 7552306329090623255158861)
                    ·
                      refine ⟨2832114873408983720684573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7552306329090623255158861 2832114873408983720684573)
                      ·
                        rfl

theorem cell23_5515524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_5515524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515524 prefixEnd_5515524 := by exact prefixLift 5515524
  have htrace : WordTrace (prefixWord ++ tailWord_5515524) baseStart_5515524 baseEnd_5515524 := by
    simpa [prefixWord, tailWord_5515524, baseEnd_5515524] using wordTrace_append hprefix tailTrace_5515524
  have hstable : (prefixWord ++ tailWord_5515524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515524).length < 2 ^ (prefixWord ++ tailWord_5515524).sum := by decide
  have hdescent : baseEnd_5515524 < baseStart_5515524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515537 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_5515537 : Nat := 118140960795 + 5515537 * 2 ^ 59
def prefixEnd_5515537 : Nat := 4983230072969 + 3 ^ 40 * 5515537 * 2
def baseEnd_5515537 : Nat := 2832121548657492169822013

theorem tailTrace_5515537 : CollatzResearch.WordTrace tailWord_5515537 prefixEnd_5515537 2832121548657492169822013 := by
  unfold tailWord_5515537
  simp only [CollatzResearch.WordTrace]
  refine ⟨201168161019158902569952865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134112107346105935046635243 201168161019158902569952865)
  ·
    refine ⟨150876120764369176927464649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201168161019158902569952865 150876120764369176927464649)
    ·
      refine ⟨113157090573276882695598487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150876120764369176927464649 113157090573276882695598487)
      ·
        refine ⟨169735635859915324043397731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113157090573276882695598487 169735635859915324043397731)
        ·
          refine ⟨254603453789872986065096597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169735635859915324043397731 254603453789872986065096597)
          ·
            refine ⟨11934536896400296221801403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 254603453789872986065096597 11934536896400296221801403)
            ·
              refine ⟨17901805344600444332702105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11934536896400296221801403 17901805344600444332702105)
              ·
                refine ⟨13426354008450333249526579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17901805344600444332702105 13426354008450333249526579)
                ·
                  refine ⟨20139531012675499874289869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13426354008450333249526579 20139531012675499874289869)
                  ·
                    refine ⟨7552324129753312452858701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20139531012675499874289869 7552324129753312452858701)
                    ·
                      refine ⟨2832121548657492169822013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7552324129753312452858701 2832121548657492169822013)
                      ·
                        rfl

theorem cell23_5515537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_5515537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515537 prefixEnd_5515537 := by exact prefixLift 5515537
  have htrace : WordTrace (prefixWord ++ tailWord_5515537) baseStart_5515537 baseEnd_5515537 := by
    simpa [prefixWord, tailWord_5515537, baseEnd_5515537] using wordTrace_append hprefix tailTrace_5515537
  have hstable : (prefixWord ++ tailWord_5515537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515537).length < 2 ^ (prefixWord ++ tailWord_5515537).sum := by decide
  have hdescent : baseEnd_5515537 < baseStart_5515537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515628 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 1, 4, 2]
def baseStart_5515628 : Nat := 118140960795 + 5515628 * 2 ^ 59
def prefixEnd_5515628 : Nat := 4983230072969 + 3 ^ 40 * 5515628 * 2
def baseEnd_5515628 : Nat := 2832168275397051313784095

theorem tailTrace_5515628 : CollatzResearch.WordTrace tailWord_5515628 prefixEnd_5515628 2832168275397051313784095 := by
  unfold tailWord_5515628
  simp only [CollatzResearch.WordTrace]
  refine ⟨100585740030914612555757769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134114320041219483407677025 100585740030914612555757769)
  ·
    refine ⟨75439305023185959416818327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100585740030914612555757769 75439305023185959416818327)
    ·
      refine ⟨113158957534778939125227491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75439305023185959416818327 113158957534778939125227491)
      ·
        refine ⟨169738436302168408687841237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113158957534778939125227491 169738436302168408687841237)
        ·
          refine ⟨3978244600832072078621279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 169738436302168408687841237 3978244600832072078621279)
          ·
            refine ⟨5967366901248108117931919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978244600832072078621279 5967366901248108117931919)
            ·
              refine ⟨8951050351872162176897879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967366901248108117931919 8951050351872162176897879)
              ·
                refine ⟨13426575527808243265346819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8951050351872162176897879 13426575527808243265346819)
                ·
                  refine ⟨20139863291712364898020229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13426575527808243265346819 20139863291712364898020229)
                  ·
                    refine ⟨3776224367196068418378793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20139863291712364898020229 3776224367196068418378793)
                    ·
                      refine ⟨2832168275397051313784095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776224367196068418378793 2832168275397051313784095)
                      ·
                        rfl

theorem cell23_5515628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_5515628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515628 prefixEnd_5515628 := by exact prefixLift 5515628
  have htrace : WordTrace (prefixWord ++ tailWord_5515628) baseStart_5515628 baseEnd_5515628 := by
    simpa [prefixWord, tailWord_5515628, baseEnd_5515628] using wordTrace_append hprefix tailTrace_5515628
  have hstable : (prefixWord ++ tailWord_5515628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515628).length < 2 ^ (prefixWord ++ tailWord_5515628).sum := by decide
  have hdescent : baseEnd_5515628 < baseStart_5515628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515651 : List Nat := [1, 1, 1, 3, 6, 2, 1, 3, 5]
def baseStart_5515651 : Nat := 118140960795 + 5515651 * 2 ^ 59
def prefixEnd_5515651 : Nat := 4983230072969 + 3 ^ 40 * 5515651 * 2
def baseEnd_5515651 : Nat := 314686676161344969310721

theorem tailTrace_5515651 : CollatzResearch.WordTrace tailWord_5515651 prefixEnd_5515651 314686676161344969310721 := by
  unfold tailWord_5515651
  simp only [CollatzResearch.WordTrace]
  refine ⟨201172318940745900039602807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134114879293830600026401871 201172318940745900039602807)
  ·
    refine ⟨301758478411118850059404211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201172318940745900039602807 301758478411118850059404211)
    ·
      refine ⟨452637717616678275089106317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301758478411118850059404211 452637717616678275089106317)
      ·
        refine ⟨169739144106254353158414869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 452637717616678275089106317 169739144106254353158414869)
        ·
          refine ⟨7956522379980672804300697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169739144106254353158414869 7956522379980672804300697)
          ·
            refine ⟨5967391784985504603225523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7956522379980672804300697 5967391784985504603225523)
            ·
              refine ⟨8951087677478256904838285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967391784985504603225523 8951087677478256904838285)
              ·
                refine ⟨3356657879054346339314357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8951087677478256904838285 3356657879054346339314357)
                ·
                  refine ⟨314686676161344969310721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356657879054346339314357 314686676161344969310721)
                  ·
                    rfl

theorem cell23_5515651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 5].length) (baseStart_5515651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515651 prefixEnd_5515651 := by exact prefixLift 5515651
  have htrace : WordTrace (prefixWord ++ tailWord_5515651) baseStart_5515651 baseEnd_5515651 := by
    simpa [prefixWord, tailWord_5515651, baseEnd_5515651] using wordTrace_append hprefix tailTrace_5515651
  have hstable : (prefixWord ++ tailWord_5515651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515651).length < 2 ^ (prefixWord ++ tailWord_5515651).sum := by decide
  have hdescent : baseEnd_5515651 < baseStart_5515651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515668 : List Nat := [2, 4, 2, 1, 3, 1, 3, 2, 5]
def baseStart_5515668 : Nat := 118140960795 + 5515668 * 2 ^ 59
def prefixEnd_5515668 : Nat := 4983230072969 + 3 ^ 40 * 5515668 * 2
def baseEnd_5515668 : Nat := 314687646069247906364879

theorem tailTrace_5515668 : CollatzResearch.WordTrace tailWord_5515668 prefixEnd_5515668 314687646069247906364879 := by
  unfold tailWord_5515668
  simp only [CollatzResearch.WordTrace]
  refine ⟨100586469490842155971485829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134115292654456207961981105 100586469490842155971485829)
  ·
    refine ⟨18859963029532904244653593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100586469490842155971485829 18859963029532904244653593)
    ·
      refine ⟨14144972272149678183490195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18859963029532904244653593 14144972272149678183490195)
      ·
        refine ⟨21217458408224517275235293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14144972272149678183490195 21217458408224517275235293)
        ·
          refine ⟨7956546903084193978213235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21217458408224517275235293 7956546903084193978213235)
          ·
            refine ⟨11934820354626290967319853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956546903084193978213235 11934820354626290967319853)
            ·
              refine ⟨4475557632984859112744945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11934820354626290967319853 4475557632984859112744945)
              ·
                refine ⟨3356668224738644334558709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475557632984859112744945 3356668224738644334558709)
                ·
                  refine ⟨314687646069247906364879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356668224738644334558709 314687646069247906364879)
                  ·
                    rfl

theorem cell23_5515668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_5515668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515668 prefixEnd_5515668 := by exact prefixLift 5515668
  have htrace : WordTrace (prefixWord ++ tailWord_5515668) baseStart_5515668 baseEnd_5515668 := by
    simpa [prefixWord, tailWord_5515668, baseEnd_5515668] using wordTrace_append hprefix tailTrace_5515668
  have hstable : (prefixWord ++ tailWord_5515668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515668).length < 2 ^ (prefixWord ++ tailWord_5515668).sum := by decide
  have hdescent : baseEnd_5515668 < baseStart_5515668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515684 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_5515684 : Nat := 118140960795 + 5515684 * 2 ^ 59
def prefixEnd_5515684 : Nat := 4983230072969 + 3 ^ 40 * 5515684 * 2
def baseEnd_5515684 : Nat := 2832197030313703094683837

theorem tailTrace_5515684 : CollatzResearch.WordTrace tailWord_5515684 prefixEnd_5515684 2832197030313703094683837 := by
  unfold tailWord_5515684
  simp only [CollatzResearch.WordTrace]
  refine ⟨100586761274813173337777053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134115681699750897783702737 100586761274813173337777053)
  ·
    refine ⟨37720035478054940001666395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100586761274813173337777053 37720035478054940001666395)
    ·
      refine ⟨56580053217082410002499593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37720035478054940001666395 56580053217082410002499593)
      ·
        refine ⟨42435039912811807501874695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56580053217082410002499593 42435039912811807501874695)
        ·
          refine ⟨63652559869217711252812043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42435039912811807501874695 63652559869217711252812043)
          ·
            refine ⟨95478839803826566879218065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63652559869217711252812043 95478839803826566879218065)
            ·
              refine ⟨71609129852869925159413549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95478839803826566879218065 71609129852869925159413549)
              ·
                refine ⟨26853423694826221934780081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71609129852869925159413549 26853423694826221934780081)
                ·
                  refine ⟨20140067771119666451085061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26853423694826221934780081 20140067771119666451085061)
                  ·
                    refine ⟨3776262707084937459578449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20140067771119666451085061 3776262707084937459578449)
                    ·
                      refine ⟨2832197030313703094683837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776262707084937459578449 2832197030313703094683837)
                      ·
                        rfl

theorem cell23_5515684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_5515684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515684 prefixEnd_5515684 := by exact prefixLift 5515684
  have htrace : WordTrace (prefixWord ++ tailWord_5515684) baseStart_5515684 baseEnd_5515684 := by
    simpa [prefixWord, tailWord_5515684, baseEnd_5515684] using wordTrace_append hprefix tailTrace_5515684
  have hstable : (prefixWord ++ tailWord_5515684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515684).length < 2 ^ (prefixWord ++ tailWord_5515684).sum := by decide
  have hdescent : baseEnd_5515684 < baseStart_5515684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515701 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_5515701 : Nat := 118140960795 + 5515701 * 2 ^ 59
def prefixEnd_5515701 : Nat := 4983230072969 + 3 ^ 40 * 5515701 * 2
def baseEnd_5515701 : Nat := 2832205759484829528171259

theorem tailTrace_5515701 : CollatzResearch.WordTrace tailWord_5515701 prefixEnd_5515701 2832205759484829528171259 := by
  unfold tailWord_5515701
  simp only [CollatzResearch.WordTrace]
  refine ⟨201174142590564758578922957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134116095060376505719281971 201174142590564758578922957)
  ·
    refine ⟨75440303471461784467096109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201174142590564758578922957 75440303471461784467096109)
    ·
      refine ⟨28290113801798169175161041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75440303471461784467096109 28290113801798169175161041)
      ·
        refine ⟨21217585351348626881370781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28290113801798169175161041 21217585351348626881370781)
        ·
          refine ⟨7956594506755735080514043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21217585351348626881370781 7956594506755735080514043)
          ·
            refine ⟨11934891760133602620771065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956594506755735080514043 11934891760133602620771065)
            ·
              refine ⟨8951168820100201965578299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11934891760133602620771065 8951168820100201965578299)
              ·
                refine ⟨13426753230150302948367449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8951168820100201965578299 13426753230150302948367449)
                ·
                  refine ⟨10070064922612727211275587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13426753230150302948367449 10070064922612727211275587)
                  ·
                    refine ⟨15105097383919090816913381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10070064922612727211275587 15105097383919090816913381)
                    ·
                      refine ⟨2832205759484829528171259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15105097383919090816913381 2832205759484829528171259)
                      ·
                        rfl

theorem cell23_5515701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_5515701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515701 prefixEnd_5515701 := by exact prefixLift 5515701
  have htrace : WordTrace (prefixWord ++ tailWord_5515701) baseStart_5515701 baseEnd_5515701 := by
    simpa [prefixWord, tailWord_5515701, baseEnd_5515701] using wordTrace_append hprefix tailTrace_5515701
  have hstable : (prefixWord ++ tailWord_5515701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515701).length < 2 ^ (prefixWord ++ tailWord_5515701).sum := by decide
  have hdescent : baseEnd_5515701 < baseStart_5515701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515737 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 5, 5]
def baseStart_5515737 : Nat := 118140960795 + 5515737 * 2 ^ 59
def prefixEnd_5515737 : Nat := 4983230072969 + 3 ^ 40 * 5515737 * 2
def baseEnd_5515737 : Nat := 944074748262797129107031

theorem tailTrace_5515737 : CollatzResearch.WordTrace tailWord_5515737 prefixEnd_5515737 944074748262797129107031 := by
  unfold tailWord_5515737
  simp only [CollatzResearch.WordTrace]
  refine ⟨201175455618434336727233465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134116970412289557818155643 201175455618434336727233465)
  ·
    refine ⟨150881591713825752545425099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201175455618434336727233465 150881591713825752545425099)
    ·
      refine ⟨226322387570738628818137649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150881591713825752545425099 226322387570738628818137649)
      ·
        refine ⟨169741790678053971613603237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226322387570738628818137649 169741790678053971613603237)
        ·
          refine ⟨31826585752135119677550607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169741790678053971613603237 31826585752135119677550607)
          ·
            refine ⟨47739878628202679516325911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31826585752135119677550607 47739878628202679516325911)
            ·
              refine ⟨71609817942304019274488867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47739878628202679516325911 71609817942304019274488867)
              ·
                refine ⟨107414726913456028911733301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71609817942304019274488867 107414726913456028911733301)
                ·
                  refine ⟨10070130648136502710474997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107414726913456028911733301 10070130648136502710474997)
                  ·
                    refine ⟨944074748262797129107031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10070130648136502710474997 944074748262797129107031)
                    ·
                      rfl

theorem cell23_5515737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_5515737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515737 prefixEnd_5515737 := by exact prefixLift 5515737
  have htrace : WordTrace (prefixWord ++ tailWord_5515737) baseStart_5515737 baseEnd_5515737 := by
    simpa [prefixWord, tailWord_5515737, baseEnd_5515737] using wordTrace_append hprefix tailTrace_5515737
  have hstable : (prefixWord ++ tailWord_5515737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515737).length < 2 ^ (prefixWord ++ tailWord_5515737).sum := by decide
  have hdescent : baseEnd_5515737 < baseStart_5515737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515744 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 1, 5, 2]
def baseStart_5515744 : Nat := 118140960795 + 5515744 * 2 ^ 59
def prefixEnd_5515744 : Nat := 4983230072969 + 3 ^ 40 * 5515744 * 2
def baseEnd_5515744 : Nat := 2832227839152972859933561

theorem tailTrace_5515744 : CollatzResearch.WordTrace tailWord_5515744 prefixEnd_5515744 2832227839152972859933561 := by
  unfold tailWord_5515744
  simp only [CollatzResearch.WordTrace]
  refine ⟨100587855464704488461369143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134117140619605984615158857 100587855464704488461369143)
  ·
    refine ⟨150881783197056732692053715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100587855464704488461369143 150881783197056732692053715)
    ·
      refine ⟨226322674795585099038080573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150881783197056732692053715 226322674795585099038080573)
      ·
        refine ⟨84871003048344412139280215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226322674795585099038080573 84871003048344412139280215)
        ·
          refine ⟨127306504572516618208920323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84871003048344412139280215 127306504572516618208920323)
          ·
            refine ⟨190959756858774927313380485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127306504572516618208920323 190959756858774927313380485)
            ·
              refine ⟨35804954411020298871258841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190959756858774927313380485 35804954411020298871258841)
              ·
                refine ⟨26853715808265224153444131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35804954411020298871258841 26853715808265224153444131)
                ·
                  refine ⟨40280573712397836230166197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26853715808265224153444131 40280573712397836230166197)
                  ·
                    refine ⟨3776303785537297146578081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40280573712397836230166197 3776303785537297146578081)
                    ·
                      refine ⟨2832227839152972859933561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776303785537297146578081 2832227839152972859933561)
                      ·
                        rfl

theorem cell23_5515744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_5515744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515744 prefixEnd_5515744 := by exact prefixLift 5515744
  have htrace : WordTrace (prefixWord ++ tailWord_5515744) baseStart_5515744 baseEnd_5515744 := by
    simpa [prefixWord, tailWord_5515744, baseEnd_5515744] using wordTrace_append hprefix tailTrace_5515744
  have hstable : (prefixWord ++ tailWord_5515744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515744).length < 2 ^ (prefixWord ++ tailWord_5515744).sum := by decide
  have hdescent : baseEnd_5515744 < baseStart_5515744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515751 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_5515751 : Nat := 118140960795 + 5515751 * 2 ^ 59
def prefixEnd_5515751 : Nat := 4983230072969 + 3 ^ 40 * 5515751 * 2
def baseEnd_5515751 : Nat := 2832231433517554332546029

theorem tailTrace_5515751 : CollatzResearch.WordTrace tailWord_5515751 prefixEnd_5515751 2832231433517554332546029 := by
  unfold tailWord_5515751
  simp only [CollatzResearch.WordTrace]
  refine ⟨201175966240383617118243107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134117310826922411412162071 201175966240383617118243107)
  ·
    refine ⟨301763949360575425677364661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201175966240383617118243107 301763949360575425677364661)
    ·
      refine ⟨28290370252553946157252937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301763949360575425677364661 28290370252553946157252937)
      ·
        refine ⟨21217777689415459617939703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28290370252553946157252937 21217777689415459617939703)
        ·
          refine ⟨31826666534123189426909555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21217777689415459617939703 31826666534123189426909555)
          ·
            refine ⟨47739999801184784140364333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31826666534123189426909555 47739999801184784140364333)
            ·
              refine ⟨17902499925444294052636625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47739999801184784140364333 17902499925444294052636625)
              ·
                refine ⟨13426874944083220539477469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17902499925444294052636625 13426874944083220539477469)
                ·
                  refine ⟨5035078104031207702304051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13426874944083220539477469 5035078104031207702304051)
                  ·
                    refine ⟨7552617156046811553456077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5035078104031207702304051 7552617156046811553456077)
                    ·
                      refine ⟨2832231433517554332546029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7552617156046811553456077 2832231433517554332546029)
                      ·
                        rfl

theorem cell23_5515751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_5515751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515751 prefixEnd_5515751 := by exact prefixLift 5515751
  have htrace : WordTrace (prefixWord ++ tailWord_5515751) baseStart_5515751 baseEnd_5515751 := by
    simpa [prefixWord, tailWord_5515751, baseEnd_5515751] using wordTrace_append hprefix tailTrace_5515751
  have hstable : (prefixWord ++ tailWord_5515751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515751).length < 2 ^ (prefixWord ++ tailWord_5515751).sum := by decide
  have hdescent : baseEnd_5515751 < baseStart_5515751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515754 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_5515754 : Nat := 118140960795 + 5515754 * 2 ^ 59
def prefixEnd_5515754 : Nat := 4983230072969 + 3 ^ 40 * 5515754 * 2
def baseEnd_5515754 : Nat := 944077657986505940269505

theorem tailTrace_5515754 : CollatzResearch.WordTrace tailWord_5515754 prefixEnd_5515754 944077657986505940269505 := by
  unfold tailWord_5515754
  simp only [CollatzResearch.WordTrace]
  refine ⟨50294018914843187157650579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134117383772915165753734877 50294018914843187157650579)
  ·
    refine ⟨75441028372264780736475869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50294018914843187157650579 75441028372264780736475869)
    ·
      refine ⟨28290385639599292776178451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75441028372264780736475869 28290385639599292776178451)
      ·
        refine ⟨42435578459398939164267677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28290385639599292776178451 42435578459398939164267677)
        ·
          refine ⟨15913341922274602186600379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42435578459398939164267677 15913341922274602186600379)
          ·
            refine ⟨23870012883411903279900569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15913341922274602186600379 23870012883411903279900569)
            ·
              refine ⟨17902509662558927459925427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23870012883411903279900569 17902509662558927459925427)
              ·
                refine ⟨26853764493838391189888141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17902509662558927459925427 26853764493838391189888141)
                ·
                  refine ⟨10070161685189396696208053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26853764493838391189888141 10070161685189396696208053)
                  ·
                    refine ⟨944077657986505940269505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10070161685189396696208053 944077657986505940269505)
                    ·
                      rfl

theorem cell23_5515754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_5515754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515754 prefixEnd_5515754 := by exact prefixLift 5515754
  have htrace : WordTrace (prefixWord ++ tailWord_5515754) baseStart_5515754 baseEnd_5515754 := by
    simpa [prefixWord, tailWord_5515754, baseEnd_5515754] using wordTrace_append hprefix tailTrace_5515754
  have hstable : (prefixWord ++ tailWord_5515754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515754).length < 2 ^ (prefixWord ++ tailWord_5515754).sum := by decide
  have hdescent : baseEnd_5515754 < baseStart_5515754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515768 : List Nat := [2, 1, 2, 1, 1, 4, 4, 3, 1, 1, 3]
def baseStart_5515768 : Nat := 118140960795 + 5515768 * 2 ^ 59
def prefixEnd_5515768 : Nat := 4983230072969 + 3 ^ 40 * 5515768 * 2
def baseEnd_5515768 : Nat := 2832240162688680766033451

theorem tailTrace_5515768 : CollatzResearch.WordTrace tailWord_5515768 prefixEnd_5515768 2832240162688680766033451 := by
  unfold tailWord_5515768
  simp only [CollatzResearch.WordTrace]
  refine ⟨100588293140661014510805979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134117724187548019347741305 100588293140661014510805979)
  ·
    refine ⟨150882439710991521766208969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100588293140661014510805979 150882439710991521766208969)
    ·
      refine ⟨113161829783243641324656727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150882439710991521766208969 113161829783243641324656727)
      ·
        refine ⟨169742744674865461986985091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113161829783243641324656727 169742744674865461986985091)
        ·
          refine ⟨254614117012298192980477637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169742744674865461986985091 254614117012298192980477637)
          ·
            refine ⟨47740146939805911183839557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254614117012298192980477637 47740146939805911183839557)
            ·
              refine ⟨8951277551213608346969917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47740146939805911183839557 8951277551213608346969917)
              ·
                refine ⟨3356729081705103130113719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8951277551213608346969917 3356729081705103130113719)
                ·
                  refine ⟨5035093622557654695170579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356729081705103130113719 5035093622557654695170579)
                  ·
                    refine ⟨7552640433836482042755869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5035093622557654695170579 7552640433836482042755869)
                    ·
                      refine ⟨2832240162688680766033451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7552640433836482042755869 2832240162688680766033451)
                      ·
                        rfl

theorem cell23_5515768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_5515768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515768 prefixEnd_5515768 := by exact prefixLift 5515768
  have htrace : WordTrace (prefixWord ++ tailWord_5515768) baseStart_5515768 baseEnd_5515768 := by
    simpa [prefixWord, tailWord_5515768, baseEnd_5515768] using wordTrace_append hprefix tailTrace_5515768
  have hstable : (prefixWord ++ tailWord_5515768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515768).length < 2 ^ (prefixWord ++ tailWord_5515768).sum := by decide
  have hdescent : baseEnd_5515768 < baseStart_5515768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515791 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 3, 2, 2]
def baseStart_5515791 : Nat := 118140960795 + 5515791 * 2 ^ 59
def prefixEnd_5515791 : Nat := 4983230072969 + 3 ^ 40 * 5515791 * 2
def baseEnd_5515791 : Nat := 2832251972743734176045845

theorem tailTrace_5515791 : CollatzResearch.WordTrace tailWord_5515791 prefixEnd_5515791 2832251972743734176045845 := by
  unfold tailWord_5515791
  simp only [CollatzResearch.WordTrace]
  refine ⟨201177425160238703949699227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134118283440159135966466151 201177425160238703949699227)
  ·
    refine ⟨301766137740358055924548841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201177425160238703949699227 301766137740358055924548841)
    ·
      refine ⟨226324603305268541943411631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301766137740358055924548841 226324603305268541943411631)
      ·
        refine ⟨339486904957902812915117447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226324603305268541943411631 339486904957902812915117447)
        ·
          refine ⟨509230357436854219372676171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339486904957902812915117447 509230357436854219372676171)
          ·
            refine ⟨763845536155281329059014257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509230357436854219372676171 763845536155281329059014257)
            ·
              refine ⟨572884152116460996794260693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763845536155281329059014257 572884152116460996794260693)
              ·
                refine ⟨13426972315229554612365485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 572884152116460996794260693 13426972315229554612365485)
                ·
                  refine ⟨5035114618211082979637057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13426972315229554612365485 5035114618211082979637057)
                  ·
                    refine ⟨3776335963658312234727793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5035114618211082979637057 3776335963658312234727793)
                    ·
                      refine ⟨2832251972743734176045845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776335963658312234727793 2832251972743734176045845)
                      ·
                        rfl

theorem cell23_5515791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 2, 2].length) (baseStart_5515791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515791 prefixEnd_5515791 := by exact prefixLift 5515791
  have htrace : WordTrace (prefixWord ++ tailWord_5515791) baseStart_5515791 baseEnd_5515791 := by
    simpa [prefixWord, tailWord_5515791, baseEnd_5515791] using wordTrace_append hprefix tailTrace_5515791
  have hstable : (prefixWord ++ tailWord_5515791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515791).length < 2 ^ (prefixWord ++ tailWord_5515791).sum := by decide
  have hdescent : baseEnd_5515791 < baseStart_5515791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515797 : List Nat := [1, 3, 2, 1, 3, 1, 2, 10]
def baseStart_5515797 : Nat := 118140960795 + 5515797 * 2 ^ 59
def prefixEnd_5515797 : Nat := 4983230072969 + 3 ^ 40 * 5515797 * 2
def baseEnd_5515797 : Nat := 104898335319543005650771

theorem tailTrace_5515797 : CollatzResearch.WordTrace tailWord_5515797 prefixEnd_5515797 104898335319543005650771 := by
  unfold tailWord_5515797
  simp only [CollatzResearch.WordTrace]
  refine ⟨201177643998216966974417645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134118429332144644649611763 201177643998216966974417645)
  ·
    refine ⟨75441616499331362615406617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201177643998216966974417645 75441616499331362615406617)
    ·
      refine ⟨56581212374498521961554963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75441616499331362615406617 56581212374498521961554963)
      ·
        refine ⟨84871818561747782942332445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56581212374498521961554963 84871818561747782942332445)
        ·
          refine ⟨31826931960655418603374667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84871818561747782942332445 31826931960655418603374667)
          ·
            refine ⟨47740397940983127905062001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31826931960655418603374667 47740397940983127905062001)
            ·
              refine ⟨35805298455737345928796501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47740397940983127905062001 35805298455737345928796501)
              ·
                refine ⟨104898335319543005650771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35805298455737345928796501 104898335319543005650771)
                ·
                  rfl

theorem cell23_5515797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 10].length) (baseStart_5515797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515797 prefixEnd_5515797 := by exact prefixLift 5515797
  have htrace : WordTrace (prefixWord ++ tailWord_5515797) baseStart_5515797 baseEnd_5515797 := by
    simpa [prefixWord, tailWord_5515797, baseEnd_5515797] using wordTrace_append hprefix tailTrace_5515797
  have hstable : (prefixWord ++ tailWord_5515797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515797).length < 2 ^ (prefixWord ++ tailWord_5515797).sum := by decide
  have hdescent : baseEnd_5515797 < baseStart_5515797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
