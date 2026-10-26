import V185TrunkScan23Chunk0973

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5764802 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_5764802 : Nat := 118140960795 + 5764802 * 2 ^ 59
def prefixEnd_5764802 : Nat := 4983230072969 + 3 ^ 40 * 5764802 * 2
def baseEnd_5764802 : Nat := 2960114304000459419363165

theorem tailTrace_5764802 : CollatzResearch.WordTrace tailWord_5764802 prefixEnd_5764802 2960114304000459419363165 := by
  unfold tailWord_5764802
  simp only [CollatzResearch.WordTrace]
  refine ⟨52564900615278594660674165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140173068307409585761797773 52564900615278594660674165)
  ·
    refine ⟨4927959432682368249438203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52564900615278594660674165 4927959432682368249438203)
    ·
      refine ⟨7391939149023552374157305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4927959432682368249438203 7391939149023552374157305)
      ·
        refine ⟨5543954361767664280617979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7391939149023552374157305 5543954361767664280617979)
        ·
          refine ⟨8315931542651496420926969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5543954361767664280617979 8315931542651496420926969)
          ·
            refine ⟨6236948656988622315695227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8315931542651496420926969 6236948656988622315695227)
            ·
              refine ⟨9355422985482933473542841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6236948656988622315695227 9355422985482933473542841)
              ·
                refine ⟨7016567239112200105157131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9355422985482933473542841 7016567239112200105157131)
                ·
                  refine ⟨10524850858668300157735697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7016567239112200105157131 10524850858668300157735697)
                  ·
                    refine ⟨7893638144001225118301773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10524850858668300157735697 7893638144001225118301773)
                    ·
                      refine ⟨2960114304000459419363165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893638144001225118301773 2960114304000459419363165)
                      ·
                        rfl

theorem cell23_5764802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_5764802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764802 prefixEnd_5764802 := by exact prefixLift 5764802
  have htrace : WordTrace (prefixWord ++ tailWord_5764802) baseStart_5764802 baseEnd_5764802 := by
    simpa [prefixWord, tailWord_5764802, baseEnd_5764802] using wordTrace_append hprefix tailTrace_5764802
  have hstable : (prefixWord ++ tailWord_5764802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764802).length < 2 ^ (prefixWord ++ tailWord_5764802).sum := by decide
  have hdescent : baseEnd_5764802 < baseStart_5764802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764854 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_5764854 : Nat := 118140960795 + 5764854 * 2 ^ 59
def prefixEnd_5764854 : Nat := 4983230072969 + 3 ^ 40 * 5764854 * 2
def baseEnd_5764854 : Nat := 2960141004994493215912925

theorem tailTrace_5764854 : CollatzResearch.WordTrace tailWord_5764854 prefixEnd_5764854 2960141004994493215912925 := by
  unfold tailWord_5764854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13141343691057874470224351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140174332704617327682393077 13141343691057874470224351)
  ·
    refine ⟨19712015536586811705336527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13141343691057874470224351 19712015536586811705336527)
    ·
      refine ⟨29568023304880217558004791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19712015536586811705336527 29568023304880217558004791)
      ·
        refine ⟨44352034957320326337007187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29568023304880217558004791 44352034957320326337007187)
        ·
          refine ⟨66528052435980489505510781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44352034957320326337007187 66528052435980489505510781)
          ·
            refine ⟨24948019663492683564566543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66528052435980489505510781 24948019663492683564566543)
            ·
              refine ⟨37422029495239025346849815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24948019663492683564566543 37422029495239025346849815)
              ·
                refine ⟨56133044242858538020274723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37422029495239025346849815 56133044242858538020274723)
                ·
                  refine ⟨84199566364287807030412085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56133044242858538020274723 84199566364287807030412085)
                  ·
                    refine ⟨7893709346651981909101133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84199566364287807030412085 7893709346651981909101133)
                    ·
                      refine ⟨2960141004994493215912925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893709346651981909101133 2960141004994493215912925)
                      ·
                        rfl

theorem cell23_5764854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_5764854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764854 prefixEnd_5764854 := by exact prefixLift 5764854
  have htrace : WordTrace (prefixWord ++ tailWord_5764854) baseStart_5764854 baseEnd_5764854 := by
    simpa [prefixWord, tailWord_5764854, baseEnd_5764854] using wordTrace_append hprefix tailTrace_5764854
  have hstable : (prefixWord ++ tailWord_5764854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764854).length < 2 ^ (prefixWord ++ tailWord_5764854).sum := by decide
  have hdescent : baseEnd_5764854 < baseStart_5764854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764874 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_5764874 : Nat := 118140960795 + 5764874 * 2 ^ 59
def prefixEnd_5764874 : Nat := 4983230072969 + 3 ^ 40 * 5764874 * 2
def baseEnd_5764874 : Nat := 986717091535861045887611

theorem tailTrace_5764874 : CollatzResearch.WordTrace tailWord_5764874 prefixEnd_5764874 986717091535861045887611 := by
  unfold tailWord_5764874
  simp only [CollatzResearch.WordTrace]
  refine ⟨52565557129213383734829419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140174819011235689959545117 52565557129213383734829419)
  ·
    refine ⟨78848335693820075602244129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52565557129213383734829419 78848335693820075602244129)
    ·
      refine ⟨59136251770365056701683097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78848335693820075602244129 59136251770365056701683097)
      ·
        refine ⟨44352188827773792526262323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59136251770365056701683097 44352188827773792526262323)
        ·
          refine ⟨66528283241660688789393485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44352188827773792526262323 66528283241660688789393485)
          ·
            refine ⟨24948106215622758296022557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66528283241660688789393485 24948106215622758296022557)
            ·
              refine ⟨9355539830858534361008459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24948106215622758296022557 9355539830858534361008459)
              ·
                refine ⟨14033309746287801541512689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9355539830858534361008459 14033309746287801541512689)
                ·
                  refine ⟨10524982309715851156134517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14033309746287801541512689 10524982309715851156134517)
                  ·
                    refine ⟨986717091535861045887611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10524982309715851156134517 986717091535861045887611)
                    ·
                      rfl

theorem cell23_5764874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_5764874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764874 prefixEnd_5764874 := by exact prefixLift 5764874
  have htrace : WordTrace (prefixWord ++ tailWord_5764874) baseStart_5764874 baseEnd_5764874 := by
    simpa [prefixWord, tailWord_5764874, baseEnd_5764874] using wordTrace_append hprefix tailTrace_5764874
  have hstable : (prefixWord ++ tailWord_5764874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764874).length < 2 ^ (prefixWord ++ tailWord_5764874).sum := by decide
  have hdescent : baseEnd_5764874 < baseStart_5764874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764914 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_5764914 : Nat := 118140960795 + 5764914 * 2 ^ 59
def prefixEnd_5764914 : Nat := 4983230072969 + 3 ^ 40 * 5764914 * 2
def baseEnd_5764914 : Nat := 2960171813833762981162649

theorem tailTrace_5764914 : CollatzResearch.WordTrace tailWord_5764914 prefixEnd_5764914 2960171813833762981162649 := by
  unfold tailWord_5764914
  simp only [CollatzResearch.WordTrace]
  refine ⟨52565921859177155442693449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140175791624472414513849197 52565921859177155442693449)
  ·
    refine ⟨39424441394382866582020087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52565921859177155442693449 39424441394382866582020087)
    ·
      refine ⟨59136662091574299873030131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39424441394382866582020087 59136662091574299873030131)
      ·
        refine ⟨88704993137361449809545197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59136662091574299873030131 88704993137361449809545197)
        ·
          refine ⟨33264372426510543678579449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88704993137361449809545197 33264372426510543678579449)
          ·
            refine ⟨24948279319882907758934587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33264372426510543678579449 24948279319882907758934587)
            ·
              refine ⟨37422418979824361638401881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24948279319882907758934587 37422418979824361638401881)
              ·
                refine ⟨28066814234868271228801411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37422418979824361638401881 28066814234868271228801411)
                ·
                  refine ⟨42100221352302406843202117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28066814234868271228801411 42100221352302406843202117)
                  ·
                    refine ⟨7893791503556701283100397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42100221352302406843202117 7893791503556701283100397)
                    ·
                      refine ⟨2960171813833762981162649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893791503556701283100397 2960171813833762981162649)
                      ·
                        rfl

theorem cell23_5764914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_5764914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764914 prefixEnd_5764914 := by exact prefixLift 5764914
  have htrace : WordTrace (prefixWord ++ tailWord_5764914) baseStart_5764914 baseEnd_5764914 := by
    simpa [prefixWord, tailWord_5764914, baseEnd_5764914] using wordTrace_append hprefix tailTrace_5764914
  have hstable : (prefixWord ++ tailWord_5764914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764914).length < 2 ^ (prefixWord ++ tailWord_5764914).sum := by decide
  have hdescent : baseEnd_5764914 < baseStart_5764914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764947 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 7, 5]
def baseStart_5764947 : Nat := 118140960795 + 5764947 * 2 ^ 59
def prefixEnd_5764947 : Nat := 4983230072969 + 3 ^ 40 * 5764947 * 2
def baseEnd_5764947 : Nat := 986729586231787117349999

theorem tailTrace_5764947 : CollatzResearch.WordTrace tailWord_5764947 prefixEnd_5764947 986729586231787117349999 := by
  unfold tailWord_5764947
  simp only [CollatzResearch.WordTrace]
  refine ⟨210264891045589068406725095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140176594030392712271150063 210264891045589068406725095)
  ·
    refine ⟨315397336568383602610087643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210264891045589068406725095 315397336568383602610087643)
    ·
      refine ⟨473096004852575403915131465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315397336568383602610087643 473096004852575403915131465)
      ·
        refine ⟨354822003639431552936348599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473096004852575403915131465 354822003639431552936348599)
        ·
          refine ⟨532233005459147329404522899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354822003639431552936348599 532233005459147329404522899)
          ·
            refine ⟨798349508188720994106784349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532233005459147329404522899 798349508188720994106784349)
            ·
              refine ⟨299381065570770372790044131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798349508188720994106784349 299381065570770372790044131)
              ·
                refine ⟨449071598356155559185066197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299381065570770372790044131 449071598356155559185066197)
                ·
                  refine ⟨10525115586472395918399989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 449071598356155559185066197 10525115586472395918399989)
                  ·
                    refine ⟨986729586231787117349999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10525115586472395918399989 986729586231787117349999)
                    ·
                      rfl

theorem cell23_5764947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 5].length) (baseStart_5764947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764947 prefixEnd_5764947 := by exact prefixLift 5764947
  have htrace : WordTrace (prefixWord ++ tailWord_5764947) baseStart_5764947 baseEnd_5764947 := by
    simpa [prefixWord, tailWord_5764947, baseEnd_5764947] using wordTrace_append hprefix tailTrace_5764947
  have hstable : (prefixWord ++ tailWord_5764947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764947).length < 2 ^ (prefixWord ++ tailWord_5764947).sum := by decide
  have hdescent : baseEnd_5764947 < baseStart_5764947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765012 : List Nat := [2, 4, 2, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_5765012 : Nat := 118140960795 + 5765012 * 2 ^ 59
def prefixEnd_5765012 : Nat := 4983230072969 + 3 ^ 40 * 5765012 * 2
def baseEnd_5765012 : Nat := 2960222134937903597737199

theorem tailTrace_5765012 : CollatzResearch.WordTrace tailWord_5765012 prefixEnd_5765012 2960222134937903597737199 := by
  unfold tailWord_5765012
  simp only [CollatzResearch.WordTrace]
  refine ⟨105133630895176792253920645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140178174526902389671894193 105133630895176792253920645)
  ·
    refine ⟨19712555792845648547610121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105133630895176792253920645 19712555792845648547610121)
    ·
      refine ⟨14784416844634236410707591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19712555792845648547610121 14784416844634236410707591)
      ·
        refine ⟨22176625266951354616061387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14784416844634236410707591 22176625266951354616061387)
        ·
          refine ⟨33264937900427031924092081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22176625266951354616061387 33264937900427031924092081)
          ·
            refine ⟨24948703425320273943069061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33264937900427031924092081 24948703425320273943069061)
            ·
              refine ⟨4677881892247551364325449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24948703425320273943069061 4677881892247551364325449)
              ·
                refine ⟨3508411419185663523244087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677881892247551364325449 3508411419185663523244087)
                ·
                  refine ⟨5262617128778495284866131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508411419185663523244087 5262617128778495284866131)
                  ·
                    refine ⟨7893925693167742927299197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5262617128778495284866131 7893925693167742927299197)
                    ·
                      refine ⟨2960222134937903597737199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893925693167742927299197 2960222134937903597737199)
                      ·
                        rfl

theorem cell23_5765012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_5765012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765012 prefixEnd_5765012 := by exact prefixLift 5765012
  have htrace : WordTrace (prefixWord ++ tailWord_5765012) baseStart_5765012 baseEnd_5765012 := by
    simpa [prefixWord, tailWord_5765012, baseEnd_5765012] using wordTrace_append hprefix tailTrace_5765012
  have hstable : (prefixWord ++ tailWord_5765012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765012).length < 2 ^ (prefixWord ++ tailWord_5765012).sum := by decide
  have hdescent : baseEnd_5765012 < baseStart_5765012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765021 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_5765021 : Nat := 118140960795 + 5765021 * 2 ^ 59
def prefixEnd_5765021 : Nat := 4983230072969 + 3 ^ 40 * 5765021 * 2
def baseEnd_5765021 : Nat := 2960226756263794062524657

theorem tailTrace_5765021 : CollatzResearch.WordTrace tailWord_5765021 prefixEnd_5765021 2960226756263794062524657 := by
  unfold tailWord_5765021
  simp only [CollatzResearch.WordTrace]
  refine ⟨210267590047320979044918917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140178393364880652696612611 210267590047320979044918917)
  ·
    refine ⟨39425173133872683570922297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210267590047320979044918917 39425173133872683570922297)
    ·
      refine ⟨29568879850404512678191723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39425173133872683570922297 29568879850404512678191723)
      ·
        refine ⟨44353319775606769017287585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29568879850404512678191723 44353319775606769017287585)
        ·
          refine ⟨33264989831705076762965689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44353319775606769017287585 33264989831705076762965689)
          ·
            refine ⟨24948742373778807572224267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33264989831705076762965689 24948742373778807572224267)
            ·
              refine ⟨37423113560668211358336401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24948742373778807572224267 37423113560668211358336401)
              ·
                refine ⟨28067335170501158518752301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37423113560668211358336401 28067335170501158518752301)
                ·
                  refine ⟨10525250688937934444532113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28067335170501158518752301 10525250688937934444532113)
                  ·
                    refine ⟨7893938016703450833399085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10525250688937934444532113 7893938016703450833399085)
                    ·
                      refine ⟨2960226756263794062524657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893938016703450833399085 2960226756263794062524657)
                      ·
                        rfl

theorem cell23_5765021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_5765021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765021 prefixEnd_5765021 := by exact prefixLift 5765021
  have htrace : WordTrace (prefixWord ++ tailWord_5765021) baseStart_5765021 baseEnd_5765021 := by
    simpa [prefixWord, tailWord_5765021, baseEnd_5765021] using wordTrace_append hprefix tailTrace_5765021
  have hstable : (prefixWord ++ tailWord_5765021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765021).length < 2 ^ (prefixWord ++ tailWord_5765021).sum := by decide
  have hdescent : baseEnd_5765021 < baseStart_5765021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765031 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_5765031 : Nat := 118140960795 + 5765031 * 2 ^ 59
def prefixEnd_5765031 : Nat := 4983230072969 + 3 ^ 40 * 5765031 * 2
def baseEnd_5765031 : Nat := 2960231891070339023399611

theorem tailTrace_5765031 : CollatzResearch.WordTrace tailWord_5765031 prefixEnd_5765031 2960231891070339023399611 := by
  unfold tailWord_5765031
  simp only [CollatzResearch.WordTrace]
  refine ⟨210267954777284750752782947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140178636518189833835188631 210267954777284750752782947)
  ·
    refine ⟨315401932165927126129174421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210267954777284750752782947 315401932165927126129174421)
    ·
      refine ⟨14784465570277834037305051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 315401932165927126129174421 14784465570277834037305051)
      ·
        refine ⟨22176698355416751055957577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14784465570277834037305051 22176698355416751055957577)
        ·
          refine ⟨16632523766562563291968183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22176698355416751055957577 16632523766562563291968183)
          ·
            refine ⟨24948785649843844937952275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16632523766562563291968183 24948785649843844937952275)
            ·
              refine ⟨37423178474765767406928413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24948785649843844937952275 37423178474765767406928413)
              ·
                refine ⟨14033691928037162777598155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37423178474765767406928413 14033691928037162777598155)
                ·
                  refine ⟨21050537892055744166397233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14033691928037162777598155 21050537892055744166397233)
                  ·
                    refine ⟨15787903419041808124797925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21050537892055744166397233 15787903419041808124797925)
                    ·
                      refine ⟨2960231891070339023399611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15787903419041808124797925 2960231891070339023399611)
                      ·
                        rfl

theorem cell23_5765031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_5765031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765031 prefixEnd_5765031 := by exact prefixLift 5765031
  have htrace : WordTrace (prefixWord ++ tailWord_5765031) baseStart_5765031 baseEnd_5765031 := by
    simpa [prefixWord, tailWord_5765031, baseEnd_5765031] using wordTrace_append hprefix tailTrace_5765031
  have hstable : (prefixWord ++ tailWord_5765031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765031).length < 2 ^ (prefixWord ++ tailWord_5765031).sum := by decide
  have hdescent : baseEnd_5765031 < baseStart_5765031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765041 : List Nat := [1, 2, 2, 4, 2, 2, 3, 7]
def baseStart_5765041 : Nat := 118140960795 + 5765041 * 2 ^ 59
def prefixEnd_5765041 : Nat := 4983230072969 + 3 ^ 40 * 5765041 * 2
def baseEnd_5765041 : Nat := 109638408365810517936095

theorem tailTrace_5765041 : CollatzResearch.WordTrace tailWord_5765041 prefixEnd_5765041 109638408365810517936095 := by
  unfold tailWord_5765041
  simp only [CollatzResearch.WordTrace]
  refine ⟨210268319507248522460646977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140178879671499014973764651 210268319507248522460646977)
  ·
    refine ⟨157701239630436391845485233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210268319507248522460646977 157701239630436391845485233)
    ·
      refine ⟨118275929722827293884113925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157701239630436391845485233 118275929722827293884113925)
      ·
        refine ⟨22176736823030117603271361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118275929722827293884113925 22176736823030117603271361)
        ·
          refine ⟨16632552617272588202453521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22176736823030117603271361 16632552617272588202453521)
          ·
            refine ⟨12474414462954441151840141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16632552617272588202453521 12474414462954441151840141)
            ·
              refine ⟨4677905423607915431940053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12474414462954441151840141 4677905423607915431940053)
              ·
                refine ⟨109638408365810517936095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4677905423607915431940053 109638408365810517936095)
                ·
                  rfl

theorem cell23_5765041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 7].length) (baseStart_5765041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765041 prefixEnd_5765041 := by exact prefixLift 5765041
  have htrace : WordTrace (prefixWord ++ tailWord_5765041) baseStart_5765041 baseEnd_5765041 := by
    simpa [prefixWord, tailWord_5765041, baseEnd_5765041] using wordTrace_append hprefix tailTrace_5765041
  have hstable : (prefixWord ++ tailWord_5765041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765041).length < 2 ^ (prefixWord ++ tailWord_5765041).sum := by decide
  have hdescent : baseEnd_5765041 < baseStart_5765041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765052 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5765052 : Nat := 118140960795 + 5765052 * 2 ^ 59
def prefixEnd_5765052 : Nat := 4983230072969 + 3 ^ 40 * 5765052 * 2
def baseEnd_5765052 : Nat := 2960242674164083441237015

theorem tailTrace_5765052 : CollatzResearch.WordTrace tailWord_5765052 prefixEnd_5765052 2960242674164083441237015 := by
  unfold tailWord_5765052
  simp only [CollatzResearch.WordTrace]
  refine ⟨105134360355104335669648705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140179147140139114226198273 105134360355104335669648705)
  ·
    refine ⟨78850770266328251752236529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105134360355104335669648705 78850770266328251752236529)
    ·
      refine ⟨59138077699746188814177397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78850770266328251752236529 59138077699746188814177397)
      ·
        refine ⟨5544194784351205201329131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59138077699746188814177397 5544194784351205201329131)
        ·
          refine ⟨8316292176526807801993697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5544194784351205201329131 8316292176526807801993697)
          ·
            refine ⟨6237219132395105851495273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8316292176526807801993697 6237219132395105851495273)
            ·
              refine ⟨4677914349296329388621455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6237219132395105851495273 4677914349296329388621455)
              ·
                refine ⟨7016871523944494082932183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677914349296329388621455 7016871523944494082932183)
                ·
                  refine ⟨10525307285916741124398275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7016871523944494082932183 10525307285916741124398275)
                  ·
                    refine ⟨15787960928875111686597413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10525307285916741124398275 15787960928875111686597413)
                    ·
                      refine ⟨2960242674164083441237015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15787960928875111686597413 2960242674164083441237015)
                      ·
                        rfl

theorem cell23_5765052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5765052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765052 prefixEnd_5765052 := by exact prefixLift 5765052
  have htrace : WordTrace (prefixWord ++ tailWord_5765052) baseStart_5765052 baseEnd_5765052 := by
    simpa [prefixWord, tailWord_5765052, baseEnd_5765052] using wordTrace_append hprefix tailTrace_5765052
  have hstable : (prefixWord ++ tailWord_5765052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765052).length < 2 ^ (prefixWord ++ tailWord_5765052).sum := by decide
  have hdescent : baseEnd_5765052 < baseStart_5765052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765061 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 5, 3, 2]
def baseStart_5765061 : Nat := 118140960795 + 5765061 * 2 ^ 59
def prefixEnd_5765061 : Nat := 4983230072969 + 3 ^ 40 * 5765061 * 2
def baseEnd_5765061 : Nat := 2960247295489973906024473

theorem tailTrace_5765061 : CollatzResearch.WordTrace tailWord_5765061 prefixEnd_5765061 2960247295489973906024473 := by
  unfold tailWord_5765061
  simp only [CollatzResearch.WordTrace]
  refine ⟨210269048967176065876375037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140179365978117377250916691 210269048967176065876375037)
  ·
    refine ⟨78850893362691024703640639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210269048967176065876375037 78850893362691024703640639)
    ·
      refine ⟨118276340044036537055460959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78850893362691024703640639 118276340044036537055460959)
      ·
        refine ⟨177414510066054805583191439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118276340044036537055460959 177414510066054805583191439)
        ·
          refine ⟨266121765099082208374787159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177414510066054805583191439 266121765099082208374787159)
          ·
            refine ⟨399182647648623312562180739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266121765099082208374787159 399182647648623312562180739)
            ·
              refine ⟨598773971472934968843271109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399182647648623312562180739 598773971472934968843271109)
              ·
                refine ⟨112270119651175306658113333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598773971472934968843271109 112270119651175306658113333)
                ·
                  refine ⟨10525323717297684999198125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112270119651175306658113333 10525323717297684999198125)
                  ·
                    refine ⟨3946996393986631874699297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10525323717297684999198125 3946996393986631874699297)
                    ·
                      refine ⟨2960247295489973906024473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946996393986631874699297 2960247295489973906024473)
                      ·
                        rfl

theorem cell23_5765061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_5765061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765061 prefixEnd_5765061 := by exact prefixLift 5765061
  have htrace : WordTrace (prefixWord ++ tailWord_5765061) baseStart_5765061 baseEnd_5765061 := by
    simpa [prefixWord, tailWord_5765061, baseEnd_5765061] using wordTrace_append hprefix tailTrace_5765061
  have hstable : (prefixWord ++ tailWord_5765061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765061).length < 2 ^ (prefixWord ++ tailWord_5765061).sum := by decide
  have hdescent : baseEnd_5765061 < baseStart_5765061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765068 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_5765068 : Nat := 118140960795 + 5765068 * 2 ^ 59
def prefixEnd_5765068 : Nat := 4983230072969 + 3 ^ 40 * 5765068 * 2
def baseEnd_5765068 : Nat := 2960250889854555378636941

theorem tailTrace_5765068 : CollatzResearch.WordTrace tailWord_5765068 prefixEnd_5765068 2960250889854555378636941 := by
  unfold tailWord_5765068
  simp only [CollatzResearch.WordTrace]
  refine ⟨105134652139075353035939929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140179536185433804047919905 105134652139075353035939929)
  ·
    refine ⟨78850989104306514776954947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105134652139075353035939929 78850989104306514776954947)
    ·
      refine ⟨118276483656459772165432421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78850989104306514776954947 118276483656459772165432421)
      ·
        refine ⟨22176840685586207281018579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118276483656459772165432421 22176840685586207281018579)
        ·
          refine ⟨33265261028379310921527869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22176840685586207281018579 33265261028379310921527869)
          ·
            refine ⟨12474472885642241595572951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33265261028379310921527869 12474472885642241595572951)
            ·
              refine ⟨18711709328463362393359427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12474472885642241595572951 18711709328463362393359427)
              ·
                refine ⟨28067563992695043590039141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18711709328463362393359427 28067563992695043590039141)
                ·
                  refine ⟨5262668248630320673132339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28067563992695043590039141 5262668248630320673132339)
                  ·
                    refine ⟨7894002372945481009698509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5262668248630320673132339 7894002372945481009698509)
                    ·
                      refine ⟨2960250889854555378636941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7894002372945481009698509 2960250889854555378636941)
                      ·
                        rfl

theorem cell23_5765068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_5765068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765068 prefixEnd_5765068 := by exact prefixLift 5765068
  have htrace : WordTrace (prefixWord ++ tailWord_5765068) baseStart_5765068 baseEnd_5765068 := by
    simpa [prefixWord, tailWord_5765068, baseEnd_5765068] using wordTrace_append hprefix tailTrace_5765068
  have hstable : (prefixWord ++ tailWord_5765068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765068).length < 2 ^ (prefixWord ++ tailWord_5765068).sum := by decide
  have hdescent : baseEnd_5765068 < baseStart_5765068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765085 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_5765085 : Nat := 118140960795 + 5765085 * 2 ^ 59
def prefixEnd_5765085 : Nat := 4983230072969 + 3 ^ 40 * 5765085 * 2
def baseEnd_5765085 : Nat := 2960259619025681812124363

theorem tailTrace_5765085 : CollatzResearch.WordTrace tailWord_5765085 prefixEnd_5765085 2960259619025681812124363 := by
  unfold tailWord_5765085
  simp only [CollatzResearch.WordTrace]
  refine ⟨210269924319089117975248709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140179949546059411983499139 210269924319089117975248709)
  ·
    refine ⟨39425610809829209620359133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210269924319089117975248709 39425610809829209620359133)
    ·
      refine ⟨14784604053685953607634675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39425610809829209620359133 14784604053685953607634675)
      ·
        refine ⟨22176906080528930411452013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14784604053685953607634675 22176906080528930411452013)
        ·
          refine ⟨8316339780198348904294505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22176906080528930411452013 8316339780198348904294505)
          ·
            refine ⟨6237254835148761678220879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8316339780198348904294505 6237254835148761678220879)
            ·
              refine ⟨9355882252723142517331319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6237254835148761678220879 9355882252723142517331319)
              ·
                refine ⟨14033823379084713775996979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9355882252723142517331319 14033823379084713775996979)
                ·
                  refine ⟨21050735068627070663995469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14033823379084713775996979 21050735068627070663995469)
                  ·
                    refine ⟨7894025650735151498998301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21050735068627070663995469 7894025650735151498998301)
                    ·
                      refine ⟨2960259619025681812124363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7894025650735151498998301 2960259619025681812124363)
                      ·
                        rfl

theorem cell23_5765085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_5765085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765085 prefixEnd_5765085 := by exact prefixLift 5765085
  have htrace : WordTrace (prefixWord ++ tailWord_5765085) baseStart_5765085 baseEnd_5765085 := by
    simpa [prefixWord, tailWord_5765085, baseEnd_5765085] using wordTrace_append hprefix tailTrace_5765085
  have hstable : (prefixWord ++ tailWord_5765085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765085).length < 2 ^ (prefixWord ++ tailWord_5765085).sum := by decide
  have hdescent : baseEnd_5765085 < baseStart_5765085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765104 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_5765104 : Nat := 118140960795 + 5765104 * 2 ^ 59
def prefixEnd_5765104 : Nat := 4983230072969 + 3 ^ 40 * 5765104 * 2
def baseEnd_5765104 : Nat := 2960269375158117237786775

theorem tailTrace_5765104 : CollatzResearch.WordTrace tailWord_5765104 prefixEnd_5765104 2960269375158117237786775 := by
  unfold tailWord_5765104
  simp only [CollatzResearch.WordTrace]
  refine ⟨105135308653010142110095183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140180411537346856146793577 105135308653010142110095183)
  ·
    refine ⟨157702962979515213165142775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105135308653010142110095183 157702962979515213165142775)
    ·
      refine ⟨236554444469272819747714163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157702962979515213165142775 236554444469272819747714163)
      ·
        refine ⟨354831666703909229621571245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236554444469272819747714163 354831666703909229621571245)
        ·
          refine ⟨133061875013965961108089217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354831666703909229621571245 133061875013965961108089217)
          ·
            refine ⟨99796406260474470831066913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133061875013965961108089217 99796406260474470831066913)
            ·
              refine ⟨74847304695355853123300185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99796406260474470831066913 74847304695355853123300185)
              ·
                refine ⟨56135478521516889842475139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74847304695355853123300185 56135478521516889842475139)
                ·
                  refine ⟨84203217782275334763712709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56135478521516889842475139 84203217782275334763712709)
                  ·
                    refine ⟨15788103334176625268196133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84203217782275334763712709 15788103334176625268196133)
                    ·
                      refine ⟨2960269375158117237786775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15788103334176625268196133 2960269375158117237786775)
                      ·
                        rfl

theorem cell23_5765104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_5765104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765104 prefixEnd_5765104 := by exact prefixLift 5765104
  have htrace : WordTrace (prefixWord ++ tailWord_5765104) baseStart_5765104 baseEnd_5765104 := by
    simpa [prefixWord, tailWord_5765104, baseEnd_5765104] using wordTrace_append hprefix tailTrace_5765104
  have hstable : (prefixWord ++ tailWord_5765104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765104).length < 2 ^ (prefixWord ++ tailWord_5765104).sum := by decide
  have hdescent : baseEnd_5765104 < baseStart_5765104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765198 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_5765198 : Nat := 118140960795 + 5765198 * 2 ^ 59
def prefixEnd_5765198 : Nat := 4983230072969 + 3 ^ 40 * 5765198 * 2
def baseEnd_5765198 : Nat := 2960317642339639870011343

theorem tailTrace_5765198 : CollatzResearch.WordTrace tailWord_5765198 prefixEnd_5765198 2960317642339639870011343 := by
  unfold tailWord_5765198
  simp only [CollatzResearch.WordTrace]
  refine ⟨26284255720959967284264031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140182697178453158849408165 26284255720959967284264031)
  ·
    refine ⟨39426383581439950926396047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26284255720959967284264031 39426383581439950926396047)
    ·
      refine ⟨59139575372159926389594071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39426383581439950926396047 59139575372159926389594071)
      ·
        refine ⟨88709363058239889584391107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59139575372159926389594071 88709363058239889584391107)
        ·
          refine ⟨133064044587359834376586661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88709363058239889584391107 133064044587359834376586661)
          ·
            refine ⟨24949508360129968945609999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133064044587359834376586661 24949508360129968945609999)
            ·
              refine ⟨37424262540194953418414999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24949508360129968945609999 37424262540194953418414999)
              ·
                refine ⟨56136393810292430127622499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37424262540194953418414999 56136393810292430127622499)
                ·
                  refine ⟨84204590715438645191433749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56136393810292430127622499 84204590715438645191433749)
                  ·
                    refine ⟨3947090189786186493348457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84204590715438645191433749 3947090189786186493348457)
                    ·
                      refine ⟨2960317642339639870011343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3947090189786186493348457 2960317642339639870011343)
                      ·
                        rfl

theorem cell23_5765198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_5765198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765198 prefixEnd_5765198 := by exact prefixLift 5765198
  have htrace : WordTrace (prefixWord ++ tailWord_5765198) baseStart_5765198 baseEnd_5765198 := by
    simpa [prefixWord, tailWord_5765198, baseEnd_5765198] using wordTrace_append hprefix tailTrace_5765198
  have hstable : (prefixWord ++ tailWord_5765198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765198).length < 2 ^ (prefixWord ++ tailWord_5765198).sum := by decide
  have hdescent : baseEnd_5765198 < baseStart_5765198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765201 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_5765201 : Nat := 118140960795 + 5765201 * 2 ^ 59
def prefixEnd_5765201 : Nat := 4983230072969 + 3 ^ 40 * 5765201 * 2
def baseEnd_5765201 : Nat := 2960319182781603358273829

theorem tailTrace_5765201 : CollatzResearch.WordTrace tailWord_5765201 prefixEnd_5765201 2960319182781603358273829 := by
  unfold tailWord_5765201
  simp only [CollatzResearch.WordTrace]
  refine ⟨210274155186668869786471457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140182770124445913190980971 210274155186668869786471457)
  ·
    refine ⟨157705616390001652339853593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210274155186668869786471457 157705616390001652339853593)
    ·
      refine ⟨118279212292501239254890195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157705616390001652339853593 118279212292501239254890195)
      ·
        refine ⟨177418818438751858882335293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118279212292501239254890195 177418818438751858882335293)
        ·
          refine ⟨66532056914531947080875735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177418818438751858882335293 66532056914531947080875735)
          ·
            refine ⟨99798085371797920621313603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66532056914531947080875735 99798085371797920621313603)
            ·
              refine ⟨149697128057696880931970405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99798085371797920621313603 149697128057696880931970405)
              ·
                refine ⟨28068211510818165174744451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149697128057696880931970405 28068211510818165174744451)
                ·
                  refine ⟨42102317266227247762116677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28068211510818165174744451 42102317266227247762116677)
                  ·
                    refine ⟨7894184487417608955396877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42102317266227247762116677 7894184487417608955396877)
                    ·
                      refine ⟨2960319182781603358273829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7894184487417608955396877 2960319182781603358273829)
                      ·
                        rfl

theorem cell23_5765201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_5765201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765201 prefixEnd_5765201 := by exact prefixLift 5765201
  have htrace : WordTrace (prefixWord ++ tailWord_5765201) baseStart_5765201 baseEnd_5765201 := by
    simpa [prefixWord, tailWord_5765201, baseEnd_5765201] using wordTrace_append hprefix tailTrace_5765201
  have hstable : (prefixWord ++ tailWord_5765201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765201).length < 2 ^ (prefixWord ++ tailWord_5765201).sum := by decide
  have hdescent : baseEnd_5765201 < baseStart_5765201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765208 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 3, 4]
def baseStart_5765208 : Nat := 118140960795 + 5765208 * 2 ^ 59
def prefixEnd_5765208 : Nat := 4983230072969 + 3 ^ 40 * 5765208 * 2
def baseEnd_5765208 : Nat := 986774259048728276962099

theorem tailTrace_5765208 : CollatzResearch.WordTrace tailWord_5765208 prefixEnd_5765208 986774259048728276962099 := by
  unfold tailWord_5765208
  simp only [CollatzResearch.WordTrace]
  refine ⟨105137205248821754990988139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140182940331762339987984185 105137205248821754990988139)
  ·
    refine ⟨157705807873232632486482209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105137205248821754990988139 157705807873232632486482209)
    ·
      refine ⟨118279355904924474364861657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157705807873232632486482209 118279355904924474364861657)
      ·
        refine ⟨88709516928693355773646243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118279355904924474364861657 88709516928693355773646243)
        ·
          refine ⟨133064275393040033660469365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88709516928693355773646243 133064275393040033660469365)
          ·
            refine ⟨12474775818097503155669003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133064275393040033660469365 12474775818097503155669003)
            ·
              refine ⟨18712163727146254733503505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12474775818097503155669003 18712163727146254733503505)
              ·
                refine ⟨14034122795359691050127629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18712163727146254733503505 14034122795359691050127629)
                ·
                  refine ⟨5262796048259884143797861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14034122795359691050127629 5262796048259884143797861)
                  ·
                    refine ⟨986774259048728276962099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5262796048259884143797861 986774259048728276962099)
                    ·
                      rfl

theorem cell23_5765208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_5765208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765208 prefixEnd_5765208 := by exact prefixLift 5765208
  have htrace : WordTrace (prefixWord ++ tailWord_5765208) baseStart_5765208 baseEnd_5765208 := by
    simpa [prefixWord, tailWord_5765208, baseEnd_5765208] using wordTrace_append hprefix tailTrace_5765208
  have hstable : (prefixWord ++ tailWord_5765208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765208).length < 2 ^ (prefixWord ++ tailWord_5765208).sum := by decide
  have hdescent : baseEnd_5765208 < baseStart_5765208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765225 : List Nat := [1, 2, 1, 1, 1, 5, 4, 3, 1, 4]
def baseStart_5765225 : Nat := 118140960795 + 5765225 * 2 ^ 59
def prefixEnd_5765225 : Nat := 4983230072969 + 3 ^ 40 * 5765225 * 2
def baseEnd_5765225 : Nat := 986777168772437088124573

theorem tailTrace_5765225 : CollatzResearch.WordTrace tailWord_5765225 prefixEnd_5765225 986777168772437088124573 := by
  unfold tailWord_5765225
  simp only [CollatzResearch.WordTrace]
  refine ⟨210275030538581921885345129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140183353692387947923563419 210275030538581921885345129)
  ·
    refine ⟨157706272903936441414008847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210275030538581921885345129 157706272903936441414008847)
    ·
      refine ⟨236559409355904662121013271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157706272903936441414008847 236559409355904662121013271)
      ·
        refine ⟨354839114033856993181519907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236559409355904662121013271 354839114033856993181519907)
        ·
          refine ⟨532258671050785489772279861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354839114033856993181519907 532258671050785489772279861)
          ·
            refine ⟨49899250411011139666151237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 532258671050785489772279861 49899250411011139666151237)
            ·
              refine ⟨9356109452064588687403357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49899250411011139666151237 9356109452064588687403357)
              ·
                refine ⟨3508541044524220757776259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9356109452064588687403357 3508541044524220757776259)
                ·
                  refine ⟨5262811566786331136664389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508541044524220757776259 5262811566786331136664389)
                  ·
                    refine ⟨986777168772437088124573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5262811566786331136664389 986777168772437088124573)
                    ·
                      rfl

theorem cell23_5765225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 4].length) (baseStart_5765225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765225 prefixEnd_5765225 := by exact prefixLift 5765225
  have htrace : WordTrace (prefixWord ++ tailWord_5765225) baseStart_5765225 baseEnd_5765225 := by
    simpa [prefixWord, tailWord_5765225, baseEnd_5765225] using wordTrace_append hprefix tailTrace_5765225
  have hstable : (prefixWord ++ tailWord_5765225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765225).length < 2 ^ (prefixWord ++ tailWord_5765225).sum := by decide
  have hdescent : baseEnd_5765225 < baseStart_5765225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765238 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_5765238 : Nat := 118140960795 + 5765238 * 2 ^ 59
def prefixEnd_5765238 : Nat := 4983230072969 + 3 ^ 40 * 5765238 * 2
def baseEnd_5765238 : Nat := 328926464618424412612351

theorem tailTrace_5765238 : CollatzResearch.WordTrace tailWord_5765238 prefixEnd_5765238 328926464618424412612351 := by
  unfold tailWord_5765238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142219042970926569098023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140183669791689883403712245 13142219042970926569098023)
  ·
    refine ⟨19713328564456389853647035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13142219042970926569098023 19713328564456389853647035)
    ·
      refine ⟨29569992846684584780470553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19713328564456389853647035 29569992846684584780470553)
      ·
        refine ⟨22177494635013438585352915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29569992846684584780470553 22177494635013438585352915)
        ·
          refine ⟨33266241952520157878029373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22177494635013438585352915 33266241952520157878029373)
          ·
            refine ⟨12474840732195059204261015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33266241952520157878029373 12474840732195059204261015)
            ·
              refine ⟨18712261098292588806391523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12474840732195059204261015 18712261098292588806391523)
              ·
                refine ⟨28068391647438883209587285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18712261098292588806391523 28068391647438883209587285)
                ·
                  refine ⟨328926464618424412612351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28068391647438883209587285 328926464618424412612351)
                  ·
                    rfl

theorem cell23_5765238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_5765238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765238 prefixEnd_5765238 := by exact prefixLift 5765238
  have htrace : WordTrace (prefixWord ++ tailWord_5765238) baseStart_5765238 baseEnd_5765238 := by
    simpa [prefixWord, tailWord_5765238, baseEnd_5765238] using wordTrace_append hprefix tailTrace_5765238
  have hstable : (prefixWord ++ tailWord_5765238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765238).length < 2 ^ (prefixWord ++ tailWord_5765238).sum := by decide
  have hdescent : baseEnd_5765238 < baseStart_5765238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765241 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_5765241 : Nat := 118140960795 + 5765241 * 2 ^ 59
def prefixEnd_5765241 : Nat := 4983230072969 + 3 ^ 40 * 5765241 * 2
def baseEnd_5765241 : Nat := 2960339722007783201773645

theorem tailTrace_5765241 : CollatzResearch.WordTrace tailWord_5765241 prefixEnd_5765241 2960339722007783201773645 := by
  unfold tailWord_5765241
  simp only [CollatzResearch.WordTrace]
  refine ⟨210275614106523956617927577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140183742737682637745285051 210275614106523956617927577)
  ·
    refine ⟨157706710579892967463445683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210275614106523956617927577 157706710579892967463445683)
    ·
      refine ⟨236560065869839451195168525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157706710579892967463445683 236560065869839451195168525)
      ·
        refine ⟨88710024701189794198188197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236560065869839451195168525 88710024701189794198188197)
        ·
          refine ⟨16633129631473086412160287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88710024701189794198188197 16633129631473086412160287)
          ·
            refine ⟨24949694447209629618240431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16633129631473086412160287 24949694447209629618240431)
            ·
              refine ⟨37424541670814444427360647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24949694447209629618240431 37424541670814444427360647)
              ·
                refine ⟨56136812506221666641040971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37424541670814444427360647 56136812506221666641040971)
                ·
                  refine ⟨84205218759332499961561457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56136812506221666641040971 84205218759332499961561457)
                  ·
                    refine ⟨63153914069499374971171093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84205218759332499961561457 63153914069499374971171093)
                    ·
                      refine ⟨2960339722007783201773645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63153914069499374971171093 2960339722007783201773645)
                      ·
                        rfl

theorem cell23_5765241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_5765241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765241 prefixEnd_5765241 := by exact prefixLift 5765241
  have htrace : WordTrace (prefixWord ++ tailWord_5765241) baseStart_5765241 baseEnd_5765241 := by
    simpa [prefixWord, tailWord_5765241, baseEnd_5765241] using wordTrace_append hprefix tailTrace_5765241
  have hstable : (prefixWord ++ tailWord_5765241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765241).length < 2 ^ (prefixWord ++ tailWord_5765241).sum := by decide
  have hdescent : baseEnd_5765241 < baseStart_5765241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765291 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 3]
def baseStart_5765291 : Nat := 118140960795 + 5765291 * 2 ^ 59
def prefixEnd_5765291 : Nat := 4983230072969 + 3 ^ 40 * 5765291 * 2
def baseEnd_5765291 : Nat := 2960365396040508006148415

theorem tailTrace_5765291 : CollatzResearch.WordTrace tailWord_5765291 prefixEnd_5765291 2960365396040508006148415 := by
  unfold tailWord_5765291
  simp only [CollatzResearch.WordTrace]
  refine ⟨210277437756342815157247727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140184958504228543438165151 210277437756342815157247727)
  ·
    refine ⟨315416156634514222735871591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210277437756342815157247727 315416156634514222735871591)
    ·
      refine ⟨473124234951771334103807387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315416156634514222735871591 473124234951771334103807387)
      ·
        refine ⟨709686352427657001155711081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473124234951771334103807387 709686352427657001155711081)
        ·
          refine ⟨532264764320742750866783311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709686352427657001155711081 532264764320742750866783311)
          ·
            refine ⟨798397146481114126300174967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532264764320742750866783311 798397146481114126300174967)
            ·
              refine ⟨1197595719721671189450262451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798397146481114126300174967 1197595719721671189450262451)
              ·
                refine ⟨1796393579582506784175393677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197595719721671189450262451 1796393579582506784175393677)
                ·
                  refine ⟨673647592343440044065772629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1796393579582506784175393677 673647592343440044065772629)
                  ·
                    refine ⟨7894307722774688016395773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 673647592343440044065772629 7894307722774688016395773)
                    ·
                      refine ⟨2960365396040508006148415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7894307722774688016395773 2960365396040508006148415)
                      ·
                        rfl

theorem cell23_5765291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 3].length) (baseStart_5765291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765291 prefixEnd_5765291 := by exact prefixLift 5765291
  have htrace : WordTrace (prefixWord ++ tailWord_5765291) baseStart_5765291 baseEnd_5765291 := by
    simpa [prefixWord, tailWord_5765291, baseEnd_5765291] using wordTrace_append hprefix tailTrace_5765291
  have hstable : (prefixWord ++ tailWord_5765291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765291).length < 2 ^ (prefixWord ++ tailWord_5765291).sum := by decide
  have hdescent : baseEnd_5765291 < baseStart_5765291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765298 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_5765298 : Nat := 118140960795 + 5765298 * 2 ^ 59
def prefixEnd_5765298 : Nat := 4983230072969 + 3 ^ 40 * 5765298 * 2
def baseEnd_5765298 : Nat := 986789663468363159586961

theorem tailTrace_5765298 : CollatzResearch.WordTrace tailWord_5765298 prefixEnd_5765298 986789663468363159586961 := by
  unfold tailWord_5765298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52569423266829363838188137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140185128711544970235168365 52569423266829363838188137)
  ·
    refine ⟨39427067450122022878641103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52569423266829363838188137 39427067450122022878641103)
    ·
      refine ⟨59140601175183034317961655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39427067450122022878641103 59140601175183034317961655)
      ·
        refine ⟨88710901762774551476942483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59140601175183034317961655 88710901762774551476942483)
        ·
          refine ⟨133066352644161827215413725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88710901762774551476942483 133066352644161827215413725)
          ·
            refine ⟨49899882241560685205780147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133066352644161827215413725 49899882241560685205780147)
            ·
              refine ⟨74849823362341027808670221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49899882241560685205780147 74849823362341027808670221)
              ·
                refine ⟨28068683760877885428251333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74849823362341027808670221 28068683760877885428251333)
                ·
                  refine ⟨5262878205164603517797125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28068683760877885428251333 5262878205164603517797125)
                  ·
                    refine ⟨986789663468363159586961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5262878205164603517797125 986789663468363159586961)
                    ·
                      rfl

theorem cell23_5765298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_5765298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765298 prefixEnd_5765298 := by exact prefixLift 5765298
  have htrace : WordTrace (prefixWord ++ tailWord_5765298) baseStart_5765298 baseEnd_5765298 := by
    simpa [prefixWord, tailWord_5765298, baseEnd_5765298] using wordTrace_append hprefix tailTrace_5765298
  have hstable : (prefixWord ++ tailWord_5765298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765298).length < 2 ^ (prefixWord ++ tailWord_5765298).sum := by decide
  have hdescent : baseEnd_5765298 < baseStart_5765298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765338 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_5765338 : Nat := 118140960795 + 5765338 * 2 ^ 59
def prefixEnd_5765338 : Nat := 4983230072969 + 3 ^ 40 * 5765338 * 2
def baseEnd_5765338 : Nat := 2960389529631269322260699

theorem tailTrace_5765338 : CollatzResearch.WordTrace tailWord_5765338 prefixEnd_5765338 2960389529631269322260699 := by
  unfold tailWord_5765338
  simp only [CollatzResearch.WordTrace]
  refine ⟨52569787996793135546052167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140186101324781694789472445 52569787996793135546052167)
  ·
    refine ⟨78854681995189703319078251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52569787996793135546052167 78854681995189703319078251)
    ·
      refine ⟨118282022992784554978617377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78854681995189703319078251 118282022992784554978617377)
      ·
        refine ⟨88711517244588416233963033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118282022992784554978617377 88711517244588416233963033)
        ·
          refine ⟨66533637933441312175472275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88711517244588416233963033 66533637933441312175472275)
          ·
            refine ⟨99800456900161968263208413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66533637933441312175472275 99800456900161968263208413)
            ·
              refine ⟨37425171337560738098703155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99800456900161968263208413 37425171337560738098703155)
              ·
                refine ⟨56137757006341107148054733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37425171337560738098703155 56137757006341107148054733)
                ·
                  refine ⟨21051658877377915180520525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56137757006341107148054733 21051658877377915180520525)
                  ·
                    refine ⟨7894372079016718192695197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21051658877377915180520525 7894372079016718192695197)
                    ·
                      refine ⟨2960389529631269322260699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7894372079016718192695197 2960389529631269322260699)
                      ·
                        rfl

theorem cell23_5765338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_5765338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765338 prefixEnd_5765338 := by exact prefixLift 5765338
  have htrace : WordTrace (prefixWord ++ tailWord_5765338) baseStart_5765338 baseEnd_5765338 := by
    simpa [prefixWord, tailWord_5765338, baseEnd_5765338] using wordTrace_append hprefix tailTrace_5765338
  have hstable : (prefixWord ++ tailWord_5765338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765338).length < 2 ^ (prefixWord ++ tailWord_5765338).sum := by decide
  have hdescent : baseEnd_5765338 < baseStart_5765338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765372 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_5765372 : Nat := 118140960795 + 5765372 * 2 ^ 59
def prefixEnd_5765372 : Nat := 4983230072969 + 3 ^ 40 * 5765372 * 2
def baseEnd_5765372 : Nat := 2960406987973522189235543

theorem tailTrace_5765372 : CollatzResearch.WordTrace tailWord_5765372 prefixEnd_5765372 2960406987973522189235543 := by
  unfold tailWord_5765372
  simp only [CollatzResearch.WordTrace]
  refine ⟨105140196034524682995473185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140186928046032910660630913 105140196034524682995473185)
  ·
    refine ⟨78855147025893512246604889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105140196034524682995473185 78855147025893512246604889)
    ·
      refine ⟨59141360269420134184953667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78855147025893512246604889 59141360269420134184953667)
      ·
        refine ⟨88712040404130201277430501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59141360269420134184953667 88712040404130201277430501)
        ·
          refine ⟨16633507575774412739518219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88712040404130201277430501 16633507575774412739518219)
          ·
            refine ⟨24950261363661619109277329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16633507575774412739518219 24950261363661619109277329)
            ·
              refine ⟨18712696022746214331957997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24950261363661619109277329 18712696022746214331957997)
              ·
                refine ⟨7017261008529830374484249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18712696022746214331957997 7017261008529830374484249)
                ·
                  refine ⟨5262945756397372780863187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7017261008529830374484249 5262945756397372780863187)
                  ·
                    refine ⟨7894418634596059171294781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5262945756397372780863187 7894418634596059171294781)
                    ·
                      refine ⟨2960406987973522189235543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7894418634596059171294781 2960406987973522189235543)
                      ·
                        rfl

theorem cell23_5765372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_5765372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765372 prefixEnd_5765372 := by exact prefixLift 5765372
  have htrace : WordTrace (prefixWord ++ tailWord_5765372) baseStart_5765372 baseEnd_5765372 := by
    simpa [prefixWord, tailWord_5765372, baseEnd_5765372] using wordTrace_append hprefix tailTrace_5765372
  have hstable : (prefixWord ++ tailWord_5765372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765372).length < 2 ^ (prefixWord ++ tailWord_5765372).sum := by decide
  have hdescent : baseEnd_5765372 < baseStart_5765372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765399 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 1, 3, 2]
def baseStart_5765399 : Nat := 118140960795 + 5765399 * 2 ^ 59
def prefixEnd_5765399 : Nat := 4983230072969 + 3 ^ 40 * 5765399 * 2
def baseEnd_5765399 : Nat := 2960420851951193583597919

theorem tailTrace_5765399 : CollatzResearch.WordTrace tailWord_5765399 prefixEnd_5765399 2960420851951193583597919 := by
  unfold tailWord_5765399
  simp only [CollatzResearch.WordTrace]
  refine ⟨210281376839951549602179251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140187584559967699734786167 210281376839951549602179251)
  ·
    refine ⟨315422065259927324403268877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210281376839951549602179251 315422065259927324403268877)
    ·
      refine ⟨118283274472472746651225829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315422065259927324403268877 118283274472472746651225829)
      ·
        refine ⟨22178113963588639997104843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118283274472472746651225829 22178113963588639997104843)
        ·
          refine ⟨33267170945382959995657265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22178113963588639997104843 33267170945382959995657265)
          ·
            refine ⟨24950378209037219996742949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33267170945382959995657265 24950378209037219996742949)
            ·
              refine ⟨4678195914194478749389303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24950378209037219996742949 4678195914194478749389303)
              ·
                refine ⟨7017293871291718124083955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678195914194478749389303 7017293871291718124083955)
                ·
                  refine ⟨10525940806937577186125933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017293871291718124083955 10525940806937577186125933)
                  ·
                    refine ⟨3947227802601591444797225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10525940806937577186125933 3947227802601591444797225)
                    ·
                      refine ⟨2960420851951193583597919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3947227802601591444797225 2960420851951193583597919)
                      ·
                        rfl

theorem cell23_5765399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_5765399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765399 prefixEnd_5765399 := by exact prefixLift 5765399
  have htrace : WordTrace (prefixWord ++ tailWord_5765399) baseStart_5765399 baseEnd_5765399 := by
    simpa [prefixWord, tailWord_5765399, baseEnd_5765399] using wordTrace_append hprefix tailTrace_5765399
  have hstable : (prefixWord ++ tailWord_5765399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765399).length < 2 ^ (prefixWord ++ tailWord_5765399).sum := by decide
  have hdescent : baseEnd_5765399 < baseStart_5765399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765406 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5765406 : Nat := 118140960795 + 5765406 * 2 ^ 59
def prefixEnd_5765406 : Nat := 4983230072969 + 3 ^ 40 * 5765406 * 2
def baseEnd_5765406 : Nat := 2960424446315775056210387

theorem tailTrace_5765406 : CollatzResearch.WordTrace tailWord_5765406 prefixEnd_5765406 2960424446315775056210387 := by
  unfold tailWord_5765406
  simp only [CollatzResearch.WordTrace]
  refine ⟨26285204018865773724710509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140187754767284126531789381 26285204018865773724710509)
  ·
    refine ⟨9856951507074665146766441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26285204018865773724710509 9856951507074665146766441)
    ·
      refine ⟨7392713630305998860074831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9856951507074665146766441 7392713630305998860074831)
      ·
        refine ⟨11089070445458998290112247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7392713630305998860074831 11089070445458998290112247)
        ·
          refine ⟨16633605668188497435168371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11089070445458998290112247 16633605668188497435168371)
          ·
            refine ⟨24950408502282746152752557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16633605668188497435168371 24950408502282746152752557)
            ·
              refine ⟨9356403188356029807282209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24950408502282746152752557 9356403188356029807282209)
              ·
                refine ⟨7017302391267022355461657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9356403188356029807282209 7017302391267022355461657)
                ·
                  refine ⟨5262976793450266766596243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7017302391267022355461657 5262976793450266766596243)
                  ·
                    refine ⟨7894465190175400149894365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5262976793450266766596243 7894465190175400149894365)
                    ·
                      refine ⟨2960424446315775056210387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7894465190175400149894365 2960424446315775056210387)
                      ·
                        rfl

theorem cell23_5765406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5765406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765406 prefixEnd_5765406 := by exact prefixLift 5765406
  have htrace : WordTrace (prefixWord ++ tailWord_5765406) baseStart_5765406 baseEnd_5765406 := by
    simpa [prefixWord, tailWord_5765406, baseEnd_5765406] using wordTrace_append hprefix tailTrace_5765406
  have hstable : (prefixWord ++ tailWord_5765406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765406).length < 2 ^ (prefixWord ++ tailWord_5765406).sum := by decide
  have hdescent : baseEnd_5765406 < baseStart_5765406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765448 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 1, 7]
def baseStart_5765448 : Nat := 118140960795 + 5765448 * 2 ^ 59
def prefixEnd_5765448 : Nat := 4983230072969 + 3 ^ 40 * 5765448 * 2
def baseEnd_5765448 : Nat := 986815337501087963961731

theorem tailTrace_5765448 : CollatzResearch.WordTrace tailWord_5765448 prefixEnd_5765448 986815337501087963961731 := by
  unfold tailWord_5765448
  simp only [CollatzResearch.WordTrace]
  refine ⟨105141582008387015485356499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140188776011182687313808665 105141582008387015485356499)
  ·
    refine ⟨157712373012580523228034749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105141582008387015485356499 157712373012580523228034749)
    ·
      refine ⟨59142139879717696210513031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157712373012580523228034749 59142139879717696210513031)
      ·
        refine ⟨88713209819576544315769547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59142139879717696210513031 88713209819576544315769547)
        ·
          refine ⟨133069814729364816473654321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88713209819576544315769547 133069814729364816473654321)
          ·
            refine ⟨99802361047023612355240741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133069814729364816473654321 99802361047023612355240741)
            ·
              refine ⟨18712942696316927316607639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99802361047023612355240741 18712942696316927316607639)
              ·
                refine ⟨28069414044475390974911459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18712942696316927316607639 28069414044475390974911459)
                ·
                  refine ⟨42104121066713086462367189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28069414044475390974911459 42104121066713086462367189)
                  ·
                    refine ⟨986815337501087963961731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42104121066713086462367189 986815337501087963961731)
                    ·
                      rfl

theorem cell23_5765448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_5765448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765448 prefixEnd_5765448 := by exact prefixLift 5765448
  have htrace : WordTrace (prefixWord ++ tailWord_5765448) baseStart_5765448 baseEnd_5765448 := by
    simpa [prefixWord, tailWord_5765448, baseEnd_5765448] using wordTrace_append hprefix tailTrace_5765448
  have hstable : (prefixWord ++ tailWord_5765448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765448).length < 2 ^ (prefixWord ++ tailWord_5765448).sum := by decide
  have hdescent : baseEnd_5765448 < baseStart_5765448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765485 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5765485 : Nat := 118140960795 + 5765485 * 2 ^ 59
def prefixEnd_5765485 : Nat := 4983230072969 + 3 ^ 40 * 5765485 * 2
def baseEnd_5765485 : Nat := 2960465011287480247122523

theorem tailTrace_5765485 : CollatzResearch.WordTrace tailWord_5765485 prefixEnd_5765485 2960465011287480247122523 := by
  unfold tailWord_5765485
  simp only [CollatzResearch.WordTrace]
  refine ⟨210284513517639986289809909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140189675678426657526539939 210284513517639986289809909)
  ·
    refine ⟨19714173142278748714669679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210284513517639986289809909 19714173142278748714669679)
    ·
      refine ⟨29571259713418123072004519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19714173142278748714669679 29571259713418123072004519)
      ·
        refine ⟨44356889570127184608006779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29571259713418123072004519 44356889570127184608006779)
        ·
          refine ⟨66535334355190776912010169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44356889570127184608006779 66535334355190776912010169)
          ·
            refine ⟨49901500766393082684007627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66535334355190776912010169 49901500766393082684007627)
            ·
              refine ⟨74852251149589624026011441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49901500766393082684007627 74852251149589624026011441)
              ·
                refine ⟨56139188362192218019508581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74852251149589624026011441 56139188362192218019508581)
                ·
                  refine ⟨10526097817911040878657859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56139188362192218019508581 10526097817911040878657859)
                  ·
                    refine ⟨15789146726866561317986789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10526097817911040878657859 15789146726866561317986789)
                    ·
                      refine ⟨2960465011287480247122523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15789146726866561317986789 2960465011287480247122523)
                      ·
                        rfl

theorem cell23_5765485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5765485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765485 prefixEnd_5765485 := by exact prefixLift 5765485
  have htrace : WordTrace (prefixWord ++ tailWord_5765485) baseStart_5765485 baseEnd_5765485 := by
    simpa [prefixWord, tailWord_5765485, baseEnd_5765485] using wordTrace_append hprefix tailTrace_5765485
  have hstable : (prefixWord ++ tailWord_5765485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765485).length < 2 ^ (prefixWord ++ tailWord_5765485).sum := by decide
  have hdescent : baseEnd_5765485 < baseStart_5765485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765548 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_5765548 : Nat := 118140960795 + 5765548 * 2 ^ 59
def prefixEnd_5765548 : Nat := 4983230072969 + 3 ^ 40 * 5765548 * 2
def baseEnd_5765548 : Nat := 2960497360568713500634733

theorem tailTrace_5765548 : CollatzResearch.WordTrace tailWord_5765548 prefixEnd_5765548 2960497360568713500634733 := by
  unfold tailWord_5765548
  simp only [CollatzResearch.WordTrace]
  refine ⟨105143405658205874024676649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140191207544274498699568865 105143405658205874024676649)
  ·
    refine ⟨78857554243654405518507487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105143405658205874024676649 78857554243654405518507487)
    ·
      refine ⟨118286331365481608277761231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78857554243654405518507487 118286331365481608277761231)
      ·
        refine ⟨177429497048222412416641847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118286331365481608277761231 177429497048222412416641847)
        ·
          refine ⟨266144245572333618624962771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177429497048222412416641847 266144245572333618624962771)
          ·
            refine ⟨399216368358500427937444157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266144245572333618624962771 399216368358500427937444157)
            ·
              refine ⟨149706138134437660476541559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399216368358500427937444157 149706138134437660476541559)
              ·
                refine ⟨224559207201656490714812339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149706138134437660476541559 224559207201656490714812339)
                ·
                  refine ⟨336838810802484736072218509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224559207201656490714812339 336838810802484736072218509)
                  ·
                    refine ⟨126314554050931776027081941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336838810802484736072218509 126314554050931776027081941)
                    ·
                      refine ⟨2960497360568713500634733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126314554050931776027081941 2960497360568713500634733)
                      ·
                        rfl

theorem cell23_5765548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_5765548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765548 prefixEnd_5765548 := by exact prefixLift 5765548
  have htrace : WordTrace (prefixWord ++ tailWord_5765548) baseStart_5765548 baseEnd_5765548 := by
    simpa [prefixWord, tailWord_5765548, baseEnd_5765548] using wordTrace_append hprefix tailTrace_5765548
  have hstable : (prefixWord ++ tailWord_5765548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765548).length < 2 ^ (prefixWord ++ tailWord_5765548).sum := by decide
  have hdescent : baseEnd_5765548 < baseStart_5765548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765556 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5765556 : Nat := 118140960795 + 5765556 * 2 ^ 59
def prefixEnd_5765556 : Nat := 4983230072969 + 3 ^ 40 * 5765556 * 2
def baseEnd_5765556 : Nat := 2960501468413949469334697

theorem tailTrace_5765556 : CollatzResearch.WordTrace tailWord_5765556 prefixEnd_5765556 2960501468413949469334697 := by
  unfold tailWord_5765556
  simp only [CollatzResearch.WordTrace]
  refine ⟨105143551550191382707822261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140191402066921843610429681 105143551550191382707822261)
  ·
    refine ⟨9857207957830442128858337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105143551550191382707822261 9857207957830442128858337)
    ·
      refine ⟨7392905968372831596643753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9857207957830442128858337 7392905968372831596643753)
      ·
        refine ⟨5544679476279623697482815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7392905968372831596643753 5544679476279623697482815)
        ·
          refine ⟨8317019214419435546224223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5544679476279623697482815 8317019214419435546224223)
          ·
            refine ⟨12475528821629153319336335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317019214419435546224223 12475528821629153319336335)
            ·
              refine ⟨18713293232443729979004503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12475528821629153319336335 18713293232443729979004503)
              ·
                refine ⟨28069939848665594968506755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18713293232443729979004503 28069939848665594968506755)
                ·
                  refine ⟨42104909772998392452760133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28069939848665594968506755 42104909772998392452760133)
                  ·
                    refine ⟨7894670582437198584892525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42104909772998392452760133 7894670582437198584892525)
                    ·
                      refine ⟨2960501468413949469334697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7894670582437198584892525 2960501468413949469334697)
                      ·
                        rfl

theorem cell23_5765556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5765556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765556 prefixEnd_5765556 := by exact prefixLift 5765556
  have htrace : WordTrace (prefixWord ++ tailWord_5765556) baseStart_5765556 baseEnd_5765556 := by
    simpa [prefixWord, tailWord_5765556, baseEnd_5765556] using wordTrace_append hprefix tailTrace_5765556
  have hstable : (prefixWord ++ tailWord_5765556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765556).length < 2 ^ (prefixWord ++ tailWord_5765556).sum := by decide
  have hdescent : baseEnd_5765556 < baseStart_5765556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765622 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_5765622 : Nat := 118140960795 + 5765622 * 2 ^ 59
def prefixEnd_5765622 : Nat := 4983230072969 + 3 ^ 40 * 5765622 * 2
def baseEnd_5765622 : Nat := 2960535358137146211109393

theorem tailTrace_5765622 : CollatzResearch.WordTrace tailWord_5765622 prefixEnd_5765622 2960535358137146211109393 := by
  unfold tailWord_5765622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13143094394883978667971695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140193006878762439125031413 13143094394883978667971695)
  ·
    refine ⟨19714641592325968001957543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13143094394883978667971695 19714641592325968001957543)
    ·
      refine ⟨29571962388488952002936315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19714641592325968001957543 29571962388488952002936315)
      ·
        refine ⟨44357943582733428004404473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29571962388488952002936315 44357943582733428004404473)
        ·
          refine ⟨33268457687050071003303355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44357943582733428004404473 33268457687050071003303355)
          ·
            refine ⟨49902686530575106504955033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33268457687050071003303355 49902686530575106504955033)
            ·
              refine ⟨37427014897931329878716275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49902686530575106504955033 37427014897931329878716275)
              ·
                refine ⟨56140522346896994818074413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37427014897931329878716275 56140522346896994818074413)
                ·
                  refine ⟨21052695880086373056777905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56140522346896994818074413 21052695880086373056777905)
                  ·
                    refine ⟨15789521910064779792583429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21052695880086373056777905 15789521910064779792583429)
                    ·
                      refine ⟨2960535358137146211109393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15789521910064779792583429 2960535358137146211109393)
                      ·
                        rfl

theorem cell23_5765622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_5765622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765622 prefixEnd_5765622 := by exact prefixLift 5765622
  have htrace : WordTrace (prefixWord ++ tailWord_5765622) baseStart_5765622 baseEnd_5765622 := by
    simpa [prefixWord, tailWord_5765622, baseEnd_5765622] using wordTrace_append hprefix tailTrace_5765622
  have hstable : (prefixWord ++ tailWord_5765622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765622).length < 2 ^ (prefixWord ++ tailWord_5765622).sum := by decide
  have hdescent : baseEnd_5765622 < baseStart_5765622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765626 : List Nat := [3, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2]
def baseStart_5765626 : Nat := 118140960795 + 5765626 * 2 ^ 59
def prefixEnd_5765626 : Nat := 4983230072969 + 3 ^ 40 * 5765626 * 2
def baseEnd_5765626 : Nat := 2960537412059764195459375

theorem tailTrace_5765626 : CollatzResearch.WordTrace tailWord_5765626 prefixEnd_5765626 2960537412059764195459375 := by
  unfold tailWord_5765626
  simp only [CollatzResearch.WordTrace]
  refine ⟨52572414052532291842673183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140193104140086111580461821 52572414052532291842673183)
  ·
    refine ⟨78858621078798437764009775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52572414052532291842673183 78858621078798437764009775)
    ·
      refine ⟨118287931618197656646014663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78858621078798437764009775 118287931618197656646014663)
      ·
        refine ⟨177431897427296484969021995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118287931618197656646014663 177431897427296484969021995)
        ·
          refine ⟨266147846140944727453532993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177431897427296484969021995 266147846140944727453532993)
          ·
            refine ⟨199610884605708545590149745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266147846140944727453532993 199610884605708545590149745)
            ·
              refine ⟨149708163454281409192612309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199610884605708545590149745 149708163454281409192612309)
              ·
                refine ⟨3508785080959720527951851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149708163454281409192612309 3508785080959720527951851)
                ·
                  refine ⟨5263177621439580791927777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508785080959720527951851 5263177621439580791927777)
                  ·
                    refine ⟨3947383216079685593945833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5263177621439580791927777 3947383216079685593945833)
                    ·
                      refine ⟨2960537412059764195459375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3947383216079685593945833 2960537412059764195459375)
                      ·
                        rfl

theorem cell23_5765626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_5765626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765626 prefixEnd_5765626 := by exact prefixLift 5765626
  have htrace : WordTrace (prefixWord ++ tailWord_5765626) baseStart_5765626 baseEnd_5765626 := by
    simpa [prefixWord, tailWord_5765626, baseEnd_5765626] using wordTrace_append hprefix tailTrace_5765626
  have hstable : (prefixWord ++ tailWord_5765626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765626).length < 2 ^ (prefixWord ++ tailWord_5765626).sum := by decide
  have hdescent : baseEnd_5765626 < baseStart_5765626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765694 : List Nat := [4, 2, 1, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_5765694 : Nat := 118140960795 + 5765694 * 2 ^ 59
def prefixEnd_5765694 : Nat := 4983230072969 + 3 ^ 40 * 5765694 * 2
def baseEnd_5765694 : Nat := 2960572328744269929409063

theorem tailTrace_5765694 : CollatzResearch.WordTrace tailWord_5765694 prefixEnd_5765694 2960572328744269929409063 := by
  unfold tailWord_5765694
  simp only [CollatzResearch.WordTrace]
  refine ⟨26286517046735351873021017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140194757582588543322778757 26286517046735351873021017)
  ·
    refine ⟨19714887785051513904765763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26286517046735351873021017 19714887785051513904765763)
    ·
      refine ⟨29572331677577270857148645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19714887785051513904765763 29572331677577270857148645)
      ·
        refine ⟨5544812189545738285715371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29572331677577270857148645 5544812189545738285715371)
        ·
          refine ⟨8317218284318607428573057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5544812189545738285715371 8317218284318607428573057)
          ·
            refine ⟨6237913713238955571429793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8317218284318607428573057 6237913713238955571429793)
            ·
              refine ⟨4678435284929216678572345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6237913713238955571429793 4678435284929216678572345)
              ·
                refine ⟨3508826463696912508929259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4678435284929216678572345 3508826463696912508929259)
                ·
                  refine ⟨5263239695545368763393889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508826463696912508929259 5263239695545368763393889)
                  ·
                    refine ⟨3947429771659026572545417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5263239695545368763393889 3947429771659026572545417)
                    ·
                      refine ⟨2960572328744269929409063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3947429771659026572545417 2960572328744269929409063)
                      ·
                        rfl

theorem cell23_5765694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_5765694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765694 prefixEnd_5765694 := by exact prefixLift 5765694
  have htrace : WordTrace (prefixWord ++ tailWord_5765694) baseStart_5765694 baseEnd_5765694 := by
    simpa [prefixWord, tailWord_5765694, baseEnd_5765694] using wordTrace_append hprefix tailTrace_5765694
  have hstable : (prefixWord ++ tailWord_5765694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765694).length < 2 ^ (prefixWord ++ tailWord_5765694).sum := by decide
  have hdescent : baseEnd_5765694 < baseStart_5765694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765699 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 4, 2, 2]
def baseStart_5765699 : Nat := 118140960795 + 5765699 * 2 ^ 59
def prefixEnd_5765699 : Nat := 4983230072969 + 3 ^ 40 * 5765699 * 2
def baseEnd_5765699 : Nat := 2960574896147542409846539

theorem tailTrace_5765699 : CollatzResearch.WordTrace tailWord_5765699 prefixEnd_5765699 2960574896147542409846539 := by
  unfold tailWord_5765699
  simp only [CollatzResearch.WordTrace]
  refine ⟨210292318738864700838100151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140194879159243133892066767 210292318738864700838100151)
  ·
    refine ⟨315438478108297051257150227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210292318738864700838100151 315438478108297051257150227)
    ·
      refine ⟨473157717162445576885725341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315438478108297051257150227 473157717162445576885725341)
      ·
        refine ⟨177434143935917091332147003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 473157717162445576885725341 177434143935917091332147003)
        ·
          refine ⟨266151215903875636998220505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177434143935917091332147003 266151215903875636998220505)
          ·
            refine ⟨199613411927906727748665379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266151215903875636998220505 199613411927906727748665379)
            ·
              refine ⟨299420117891860091622998069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199613411927906727748665379 299420117891860091622998069)
              ·
                refine ⟨28070636052361883589656069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 299420117891860091622998069 28070636052361883589656069)
                ·
                  refine ⟨5263244259817853173060513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28070636052361883589656069 5263244259817853173060513)
                  ·
                    refine ⟨3947433194863389879795385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5263244259817853173060513 3947433194863389879795385)
                    ·
                      refine ⟨2960574896147542409846539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3947433194863389879795385 2960574896147542409846539)
                      ·
                        rfl

theorem cell23_5765699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_5765699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765699 prefixEnd_5765699 := by exact prefixLift 5765699
  have htrace : WordTrace (prefixWord ++ tailWord_5765699) baseStart_5765699 baseEnd_5765699 := by
    simpa [prefixWord, tailWord_5765699, baseEnd_5765699] using wordTrace_append hprefix tailTrace_5765699
  have hstable : (prefixWord ++ tailWord_5765699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765699).length < 2 ^ (prefixWord ++ tailWord_5765699).sum := by decide
  have hdescent : baseEnd_5765699 < baseStart_5765699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765709 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_5765709 : Nat := 118140960795 + 5765709 * 2 ^ 59
def prefixEnd_5765709 : Nat := 4983230072969 + 3 ^ 40 * 5765709 * 2
def baseEnd_5765709 : Nat := 986860010318029123573831

theorem tailTrace_5765709 : CollatzResearch.WordTrace tailWord_5765709 prefixEnd_5765709 986860010318029123573831 := by
  unfold tailWord_5765709
  simp only [CollatzResearch.WordTrace]
  refine ⟨210292683468828472545964181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140195122312552315030642787 210292683468828472545964181)
  ·
    refine ⟨9857469537601334650592071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 210292683468828472545964181 9857469537601334650592071)
    ·
      refine ⟨14786204306402001975888107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9857469537601334650592071 14786204306402001975888107)
      ·
        refine ⟨22179306459603002963832161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14786204306402001975888107 22179306459603002963832161)
        ·
          refine ⟨16634479844702252222874121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22179306459603002963832161 16634479844702252222874121)
          ·
            refine ⟨12475859883526689167155591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16634479844702252222874121 12475859883526689167155591)
            ·
              refine ⟨18713789825290033750733387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12475859883526689167155591 18713789825290033750733387)
              ·
                refine ⟨28070684737935050626100081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18713789825290033750733387 28070684737935050626100081)
                ·
                  refine ⟨21053013553451287969575061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28070684737935050626100081 21053013553451287969575061)
                  ·
                    refine ⟨986860010318029123573831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21053013553451287969575061 986860010318029123573831)
                    ·
                      rfl

theorem cell23_5765709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_5765709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765709 prefixEnd_5765709 := by exact prefixLift 5765709
  have htrace : WordTrace (prefixWord ++ tailWord_5765709) baseStart_5765709 baseEnd_5765709 := by
    simpa [prefixWord, tailWord_5765709, baseEnd_5765709] using wordTrace_append hprefix tailTrace_5765709
  have hstable : (prefixWord ++ tailWord_5765709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765709).length < 2 ^ (prefixWord ++ tailWord_5765709).sum := by decide
  have hdescent : baseEnd_5765709 < baseStart_5765709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765716 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_5765716 : Nat := 118140960795 + 5765716 * 2 ^ 59
def prefixEnd_5765716 : Nat := 4983230072969 + 3 ^ 40 * 5765716 * 2
def baseEnd_5765716 : Nat := 2960583625318668843333961

theorem tailTrace_5765716 : CollatzResearch.WordTrace tailWord_5765716 prefixEnd_5765716 2960583625318668843333961 := by
  unfold tailWord_5765716
  simp only [CollatzResearch.WordTrace]
  refine ⟨105146469389901556370734501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140195292519868741827646001 105146469389901556370734501)
  ·
    refine ⟨19714963010606541819512719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105146469389901556370734501 19714963010606541819512719)
    ·
      refine ⟨29572444515909812729269079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19714963010606541819512719 29572444515909812729269079)
      ·
        refine ⟨44358666773864719093903619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29572444515909812729269079 44358666773864719093903619)
        ·
          refine ⟨66538000160797078640855429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44358666773864719093903619 66538000160797078640855429)
          ·
            refine ⟨12475875030149452245160393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66538000160797078640855429 12475875030149452245160393)
            ·
              refine ⟨9356906272612089183870295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12475875030149452245160393 9356906272612089183870295)
              ·
                refine ⟨14035359408918133775805443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9356906272612089183870295 14035359408918133775805443)
                ·
                  refine ⟨21053039113377200663708165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14035359408918133775805443 21053039113377200663708165)
                  ·
                    refine ⟨3947444833758225124445281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21053039113377200663708165 3947444833758225124445281)
                    ·
                      refine ⟨2960583625318668843333961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3947444833758225124445281 2960583625318668843333961)
                      ·
                        rfl

theorem cell23_5765716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_5765716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765716 prefixEnd_5765716 := by exact prefixLift 5765716
  have htrace : WordTrace (prefixWord ++ tailWord_5765716) baseStart_5765716 baseEnd_5765716 := by
    simpa [prefixWord, tailWord_5765716, baseEnd_5765716] using wordTrace_append hprefix tailTrace_5765716
  have hstable : (prefixWord ++ tailWord_5765716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765716).length < 2 ^ (prefixWord ++ tailWord_5765716).sum := by decide
  have hdescent : baseEnd_5765716 < baseStart_5765716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765732 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_5765732 : Nat := 118140960795 + 5765732 * 2 ^ 59
def prefixEnd_5765732 : Nat := 4983230072969 + 3 ^ 40 * 5765732 * 2
def baseEnd_5765732 : Nat := 2960591841009140780733887

theorem tailTrace_5765732 : CollatzResearch.WordTrace tailWord_5765732 prefixEnd_5765732 2960591841009140780733887 := by
  unfold tailWord_5765732
  simp only [CollatzResearch.WordTrace]
  refine ⟨105146761173872573737025725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140195681565163431649367633 105146761173872573737025725)
  ·
    refine ⟨39430035440202215151384647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105146761173872573737025725 39430035440202215151384647)
    ·
      refine ⟨59145053160303322727076971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39430035440202215151384647 59145053160303322727076971)
      ·
        refine ⟨88717579740454984090615457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59145053160303322727076971 88717579740454984090615457)
        ·
          refine ⟨66538184805341238067961593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88717579740454984090615457 66538184805341238067961593)
          ·
            refine ⟨49903638604005928550971195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66538184805341238067961593 49903638604005928550971195)
            ·
              refine ⟨74855457906008892826456793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49903638604005928550971195 74855457906008892826456793)
              ·
                refine ⟨56141593429506669619842595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74855457906008892826456793 56141593429506669619842595)
                ·
                  refine ⟨84212390144260004429763893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56141593429506669619842595 84212390144260004429763893)
                  ·
                    refine ⟨7894911576024375415290365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84212390144260004429763893 7894911576024375415290365)
                    ·
                      refine ⟨2960591841009140780733887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7894911576024375415290365 2960591841009140780733887)
                      ·
                        rfl

theorem cell23_5765732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_5765732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765732 prefixEnd_5765732 := by exact prefixLift 5765732
  have htrace : WordTrace (prefixWord ++ tailWord_5765732) baseStart_5765732 baseEnd_5765732 := by
    simpa [prefixWord, tailWord_5765732, baseEnd_5765732] using wordTrace_append hprefix tailTrace_5765732
  have hstable : (prefixWord ++ tailWord_5765732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765732).length < 2 ^ (prefixWord ++ tailWord_5765732).sum := by decide
  have hdescent : baseEnd_5765732 < baseStart_5765732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765772 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_5765772 : Nat := 118140960795 + 5765772 * 2 ^ 59
def prefixEnd_5765772 : Nat := 4983230072969 + 3 ^ 40 * 5765772 * 2
def baseEnd_5765772 : Nat := 2960612380235320624233703

theorem tailTrace_5765772 : CollatzResearch.WordTrace tailWord_5765772 prefixEnd_5765772 2960612380235320624233703 := by
  unfold tailWord_5765772
  simp only [CollatzResearch.WordTrace]
  refine ⟨105147490633800117152753785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140196654178400156203671713 105147490633800117152753785)
  ·
    refine ⟨78860617975350087864565339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105147490633800117152753785 78860617975350087864565339)
    ·
      refine ⟨118290926963025131796848009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78860617975350087864565339 118290926963025131796848009)
      ·
        refine ⟨88718195222268848847636007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118290926963025131796848009 88718195222268848847636007)
        ·
          refine ⟨133077292833403273271454011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88718195222268848847636007 133077292833403273271454011)
          ·
            refine ⟨199615939250104909907181017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133077292833403273271454011 199615939250104909907181017)
            ·
              refine ⟨149711954437578682430385763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199615939250104909907181017 149711954437578682430385763)
              ·
                refine ⟨224567931656368023645578645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149711954437578682430385763 224567931656368023645578645)
                ·
                  refine ⟨10526621796392251108386499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 224567931656368023645578645 10526621796392251108386499)
                  ·
                    refine ⟨15789932694588376662579749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10526621796392251108386499 15789932694588376662579749)
                    ·
                      refine ⟨2960612380235320624233703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15789932694588376662579749 2960612380235320624233703)
                      ·
                        rfl

theorem cell23_5765772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_5765772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765772 prefixEnd_5765772 := by exact prefixLift 5765772
  have htrace : WordTrace (prefixWord ++ tailWord_5765772) baseStart_5765772 baseEnd_5765772 := by
    simpa [prefixWord, tailWord_5765772, baseEnd_5765772] using wordTrace_append hprefix tailTrace_5765772
  have hstable : (prefixWord ++ tailWord_5765772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765772).length < 2 ^ (prefixWord ++ tailWord_5765772).sum := by decide
  have hdescent : baseEnd_5765772 < baseStart_5765772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765789 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_5765789 : Nat := 118140960795 + 5765789 * 2 ^ 59
def prefixEnd_5765789 : Nat := 4983230072969 + 3 ^ 40 * 5765789 * 2
def baseEnd_5765789 : Nat := 2960621109406447057721125

theorem tailTrace_5765789 : CollatzResearch.WordTrace tailWord_5765789 prefixEnd_5765789 2960621109406447057721125 := by
  unfold tailWord_5765789
  simp only [CollatzResearch.WordTrace]
  refine ⟨210295601308538646208876421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140197067539025764139250947 210295601308538646208876421)
  ·
    refine ⟨39430425245350996164164329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210295601308538646208876421 39430425245350996164164329)
    ·
      refine ⟨29572818934013247123123247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39430425245350996164164329 29572818934013247123123247)
      ·
        refine ⟨44359228401019870684684871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29572818934013247123123247 44359228401019870684684871)
        ·
          refine ⟨66538842601529806027027307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44359228401019870684684871 66538842601529806027027307)
          ·
            refine ⟨99808263902294709040540961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66538842601529806027027307 99808263902294709040540961)
            ·
              refine ⟨74856197926721031780405721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99808263902294709040540961 74856197926721031780405721)
              ·
                refine ⟨56142148445040773835304291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74856197926721031780405721 56142148445040773835304291)
                ·
                  refine ⟨84213222667561160752956437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56142148445040773835304291 84213222667561160752956437)
                  ·
                    refine ⟨3947494812541929410294833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84213222667561160752956437 3947494812541929410294833)
                    ·
                      refine ⟨2960621109406447057721125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3947494812541929410294833 2960621109406447057721125)
                      ·
                        rfl

theorem cell23_5765789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_5765789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765789 prefixEnd_5765789 := by exact prefixLift 5765789
  have htrace : WordTrace (prefixWord ++ tailWord_5765789) baseStart_5765789 baseEnd_5765789 := by
    simpa [prefixWord, tailWord_5765789, baseEnd_5765789] using wordTrace_append hprefix tailTrace_5765789
  have hstable : (prefixWord ++ tailWord_5765789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765789).length < 2 ^ (prefixWord ++ tailWord_5765789).sum := by decide
  have hdescent : baseEnd_5765789 < baseStart_5765789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765806 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5765806 : Nat := 118140960795 + 5765806 * 2 ^ 59
def prefixEnd_5765806 : Nat := 4983230072969 + 3 ^ 40 * 5765806 * 2
def baseEnd_5765806 : Nat := 2960629838577573491208547

theorem tailTrace_5765806 : CollatzResearch.WordTrace tailWord_5765806 prefixEnd_5765806 2960629838577573491208547 := by
  unfold tailWord_5765806
  simp only [CollatzResearch.WordTrace]
  refine ⟨26287027668684632264030659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140197480899651372074830181 26287027668684632264030659)
  ·
    refine ⟨39430541503026948396045989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26287027668684632264030659 39430541503026948396045989)
    ·
      refine ⟨7393226531817552824258623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39430541503026948396045989 7393226531817552824258623)
      ·
        refine ⟨11089839797726329236387935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7393226531817552824258623 11089839797726329236387935)
        ·
          refine ⟨16634759696589493854581903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11089839797726329236387935 16634759696589493854581903)
          ·
            refine ⟨24952139544884240781872855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16634759696589493854581903 24952139544884240781872855)
            ·
              refine ⟨37428209317326361172809283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24952139544884240781872855 37428209317326361172809283)
              ·
                refine ⟨56142313975989541759213925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37428209317326361172809283 56142313975989541759213925)
                ·
                  refine ⟨10526683870498039079852611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56142313975989541759213925 10526683870498039079852611)
                  ·
                    refine ⟨15790025805747058619778917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10526683870498039079852611 15790025805747058619778917)
                    ·
                      refine ⟨2960629838577573491208547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15790025805747058619778917 2960629838577573491208547)
                      ·
                        rfl

theorem cell23_5765806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5765806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765806 prefixEnd_5765806 := by exact prefixLift 5765806
  have htrace : WordTrace (prefixWord ++ tailWord_5765806) baseStart_5765806 baseEnd_5765806 := by
    simpa [prefixWord, tailWord_5765806, baseEnd_5765806] using wordTrace_append hprefix tailTrace_5765806
  have hstable : (prefixWord ++ tailWord_5765806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765806).length < 2 ^ (prefixWord ++ tailWord_5765806).sum := by decide
  have hdescent : baseEnd_5765806 < baseStart_5765806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765872 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 3, 6]
def baseStart_5765872 : Nat := 118140960795 + 5765872 * 2 ^ 59
def prefixEnd_5765872 : Nat := 4983230072969 + 3 ^ 40 * 5765872 * 2
def baseEnd_5765872 : Nat := 986887909433590077661081

theorem tailTrace_5765872 : CollatzResearch.WordTrace tailWord_5765872 prefixEnd_5765872 986887909433590077661081 := by
  unfold tailWord_5765872
  simp only [CollatzResearch.WordTrace]
  refine ⟨105149314283618975692073935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140199085711491967589431913 105149314283618975692073935)
  ·
    refine ⟨157723971425428463538110903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105149314283618975692073935 157723971425428463538110903)
    ·
      refine ⟨236585957138142695307166355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157723971425428463538110903 236585957138142695307166355)
      ·
        refine ⟨354878935707214042960749533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236585957138142695307166355 354878935707214042960749533)
        ·
          refine ⟨133079600890205266110281075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354878935707214042960749533 133079600890205266110281075)
          ·
            refine ⟨199619401335307899165421613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133079600890205266110281075 199619401335307899165421613)
            ·
              refine ⟨74857275500740462187033105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199619401335307899165421613 74857275500740462187033105)
              ·
                refine ⟨56142956625555346640274829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74857275500740462187033105 56142956625555346640274829)
                ·
                  refine ⟨21053608734583254990103061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56142956625555346640274829 21053608734583254990103061)
                  ·
                    refine ⟨986887909433590077661081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21053608734583254990103061 986887909433590077661081)
                    ·
                      rfl

theorem cell23_5765872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_5765872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765872 prefixEnd_5765872 := by exact prefixLift 5765872
  have htrace : WordTrace (prefixWord ++ tailWord_5765872) baseStart_5765872 baseEnd_5765872 := by
    simpa [prefixWord, tailWord_5765872, baseEnd_5765872] using wordTrace_append hprefix tailTrace_5765872
  have hstable : (prefixWord ++ tailWord_5765872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765872).length < 2 ^ (prefixWord ++ tailWord_5765872).sum := by decide
  have hdescent : baseEnd_5765872 < baseStart_5765872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765873 : List Nat := [1, 2, 2, 2, 2, 2, 3, 4, 1, 1, 3]
def baseStart_5765873 : Nat := 118140960795 + 5765873 * 2 ^ 59
def prefixEnd_5765873 : Nat := 4983230072969 + 3 ^ 40 * 5765873 * 2
def baseEnd_5765873 : Nat := 2960664241781424729070739

theorem tailTrace_5765873 : CollatzResearch.WordTrace tailWord_5765873 prefixEnd_5765873 2960664241781424729070739 := by
  unfold tailWord_5765873
  simp only [CollatzResearch.WordTrace]
  refine ⟨210298665040234328554934273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140199110026822885703289515 210298665040234328554934273)
  ·
    refine ⟨157723998780175746416200705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210298665040234328554934273 157723998780175746416200705)
    ·
      refine ⟨118292999085131809812150529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157723998780175746416200705 118292999085131809812150529)
      ·
        refine ⟨88719749313848857359112897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118292999085131809812150529 88719749313848857359112897)
        ·
          refine ⟨66539811985386643019334673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88719749313848857359112897 66539811985386643019334673)
          ·
            refine ⟨49904858989039982264501005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66539811985386643019334673 49904858989039982264501005)
            ·
              refine ⟨18714322120889993349187877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49904858989039982264501005 18714322120889993349187877)
              ·
                refine ⟨3508935397666873752972727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18714322120889993349187877 3508935397666873752972727)
                ·
                  refine ⟨5263403096500310629459091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508935397666873752972727 5263403096500310629459091)
                  ·
                    refine ⟨7895104644750465944188637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5263403096500310629459091 7895104644750465944188637)
                    ·
                      refine ⟨2960664241781424729070739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7895104644750465944188637 2960664241781424729070739)
                      ·
                        rfl

theorem cell23_5765873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_5765873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765873 prefixEnd_5765873 := by exact prefixLift 5765873
  have htrace : WordTrace (prefixWord ++ tailWord_5765873) baseStart_5765873 baseEnd_5765873 := by
    simpa [prefixWord, tailWord_5765873, baseEnd_5765873] using wordTrace_append hprefix tailTrace_5765873
  have hstable : (prefixWord ++ tailWord_5765873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765873).length < 2 ^ (prefixWord ++ tailWord_5765873).sum := by decide
  have hdescent : baseEnd_5765873 < baseStart_5765873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765879 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 2, 6, 2]
def baseStart_5765879 : Nat := 118140960795 + 5765879 * 2 ^ 59
def prefixEnd_5765879 : Nat := 4983230072969 + 3 ^ 40 * 5765879 * 2
def baseEnd_5765879 : Nat := 2960667322665351705595711

theorem tailTrace_5765879 : CollatzResearch.WordTrace tailWord_5765879 prefixEnd_5765879 2960667322665351705595711 := by
  unfold tailWord_5765879
  simp only [CollatzResearch.WordTrace]
  refine ⟨210298883878212591579652691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140199255918808394386435127 210298883878212591579652691)
  ·
    refine ⟨315448325817318887369479037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210298883878212591579652691 315448325817318887369479037)
    ·
      refine ⟨118293122181494582763554639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315448325817318887369479037 118293122181494582763554639)
      ·
        refine ⟨177439683272241874145331959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118293122181494582763554639 177439683272241874145331959)
        ·
          refine ⟨266159524908362811217997939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177439683272241874145331959 266159524908362811217997939)
          ·
            refine ⟨399239287362544216826996909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266159524908362811217997939 399239287362544216826996909)
            ·
              refine ⟨149714732760954081310123841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399239287362544216826996909 149714732760954081310123841)
              ·
                refine ⟨112286049570715560982592881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149714732760954081310123841 112286049570715560982592881)
                ·
                  refine ⟨84214537178036670736944661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112286049570715560982592881 84214537178036670736944661)
                  ·
                    refine ⟨3947556430220468940794281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84214537178036670736944661 3947556430220468940794281)
                    ·
                      refine ⟨2960667322665351705595711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3947556430220468940794281 2960667322665351705595711)
                      ·
                        rfl

theorem cell23_5765879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_5765879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765879 prefixEnd_5765879 := by exact prefixLift 5765879
  have htrace : WordTrace (prefixWord ++ tailWord_5765879) baseStart_5765879 baseEnd_5765879 := by
    simpa [prefixWord, tailWord_5765879, baseEnd_5765879] using wordTrace_append hprefix tailTrace_5765879
  have hstable : (prefixWord ++ tailWord_5765879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765879).length < 2 ^ (prefixWord ++ tailWord_5765879).sum := by decide
  have hdescent : baseEnd_5765879 < baseStart_5765879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765889 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 6, 4]
def baseStart_5765889 : Nat := 118140960795 + 5765889 * 2 ^ 59
def prefixEnd_5765889 : Nat := 4983230072969 + 3 ^ 40 * 5765889 * 2
def baseEnd_5765889 : Nat := 986890819157298888823555

theorem tailTrace_5765889 : CollatzResearch.WordTrace tailWord_5765889 prefixEnd_5765889 986890819157298888823555 := by
  unfold tailWord_5765889
  simp only [CollatzResearch.WordTrace]
  refine ⟨210299248608176363287516721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140199499072117575525011147 210299248608176363287516721)
  ·
    refine ⟨157724436456132272465637541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210299248608176363287516721 157724436456132272465637541)
    ·
      refine ⟨29573331835524801087307039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157724436456132272465637541 29573331835524801087307039)
      ·
        refine ⟨44359997753287201630960559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29573331835524801087307039 44359997753287201630960559)
        ·
          refine ⟨66539996629930802446440839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44359997753287201630960559 66539996629930802446440839)
          ·
            refine ⟨99809994944896203669661259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66539996629930802446440839 99809994944896203669661259)
            ·
              refine ⟨149714992417344305504491889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99809994944896203669661259 149714992417344305504491889)
              ·
                refine ⟨112286244313008229128368917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149714992417344305504491889 112286244313008229128368917)
                ·
                  refine ⟨5263417702172260740392293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112286244313008229128368917 5263417702172260740392293)
                  ·
                    refine ⟨986890819157298888823555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5263417702172260740392293 986890819157298888823555)
                    ·
                      rfl

theorem cell23_5765889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_5765889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765889 prefixEnd_5765889 := by exact prefixLift 5765889
  have htrace : WordTrace (prefixWord ++ tailWord_5765889) baseStart_5765889 baseEnd_5765889 := by
    simpa [prefixWord, tailWord_5765889, baseEnd_5765889] using wordTrace_append hprefix tailTrace_5765889
  have hstable : (prefixWord ++ tailWord_5765889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765889).length < 2 ^ (prefixWord ++ tailWord_5765889).sum := by decide
  have hdescent : baseEnd_5765889 < baseStart_5765889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765909 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_5765909 : Nat := 118140960795 + 5765909 * 2 ^ 59
def prefixEnd_5765909 : Nat := 4983230072969 + 3 ^ 40 * 5765909 * 2
def baseEnd_5765909 : Nat := 2960682727084986588220573

theorem tailTrace_5765909 : CollatzResearch.WordTrace tailWord_5765909 prefixEnd_5765909 2960682727084986588220573 := by
  unfold tailWord_5765909
  simp only [CollatzResearch.WordTrace]
  refine ⟨210299978068103906703244781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140199985378735937802163187 210299978068103906703244781)
  ·
    refine ⟨78862491775538965013716793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210299978068103906703244781 78862491775538965013716793)
    ·
      refine ⟨59146868831654223760287595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78862491775538965013716793 59146868831654223760287595)
      ·
        refine ⟨88720303247481335640431393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59146868831654223760287595 88720303247481335640431393)
        ·
          refine ⟨66540227435611001730323545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88720303247481335640431393 66540227435611001730323545)
          ·
            refine ⟨49905170576708251297742659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66540227435611001730323545 49905170576708251297742659)
            ·
              refine ⟨74857755865062376946613989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49905170576708251297742659 74857755865062376946613989)
              ·
                refine ⟨14035829224699195677490123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74857755865062376946613989 14035829224699195677490123)
                ·
                  refine ⟨21053743837048793516235185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14035829224699195677490123 21053743837048793516235185)
                  ·
                    refine ⟨15790307877786595137176389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21053743837048793516235185 15790307877786595137176389)
                    ·
                      refine ⟨2960682727084986588220573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15790307877786595137176389 2960682727084986588220573)
                      ·
                        rfl

theorem cell23_5765909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_5765909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765909 prefixEnd_5765909 := by exact prefixLift 5765909
  have htrace : WordTrace (prefixWord ++ tailWord_5765909) baseStart_5765909 baseEnd_5765909 := by
    simpa [prefixWord, tailWord_5765909, baseEnd_5765909] using wordTrace_append hprefix tailTrace_5765909
  have hstable : (prefixWord ++ tailWord_5765909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765909).length < 2 ^ (prefixWord ++ tailWord_5765909).sum := by decide
  have hdescent : baseEnd_5765909 < baseStart_5765909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765940 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_5765940 : Nat := 118140960795 + 5765940 * 2 ^ 59
def prefixEnd_5765940 : Nat := 4983230072969 + 3 ^ 40 * 5765940 * 2
def baseEnd_5765940 : Nat := 986899548328425322310977

theorem tailTrace_5765940 : CollatzResearch.WordTrace tailWord_5765940 prefixEnd_5765940 986899548328425322310977 := by
  unfold tailWord_5765940
  simp only [CollatzResearch.WordTrace]
  refine ⟨105150554365495799498811637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140200739153994399331748849 105150554365495799498811637)
  ·
    refine ⟨9857864471765231203013591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105150554365495799498811637 9857864471765231203013591)
    ·
      refine ⟨14786796707647846804520387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9857864471765231203013591 14786796707647846804520387)
      ·
        refine ⟨22180195061471770206780581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14786796707647846804520387 22180195061471770206780581)
        ·
          refine ⟨4158786574025956913771359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22180195061471770206780581 4158786574025956913771359)
          ·
            refine ⟨6238179861038935370657039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158786574025956913771359 6238179861038935370657039)
            ·
              refine ⟨9357269791558403055985559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238179861038935370657039 9357269791558403055985559)
              ·
                refine ⟨14035904687337604583978339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9357269791558403055985559 14035904687337604583978339)
                ·
                  refine ⟨21053857031006406875967509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14035904687337604583978339 21053857031006406875967509)
                  ·
                    refine ⟨986899548328425322310977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21053857031006406875967509 986899548328425322310977)
                    ·
                      rfl

theorem cell23_5765940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_5765940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765940 prefixEnd_5765940 := by exact prefixLift 5765940
  have htrace : WordTrace (prefixWord ++ tailWord_5765940) baseStart_5765940 baseEnd_5765940 := by
    simpa [prefixWord, tailWord_5765940, baseEnd_5765940] using wordTrace_append hprefix tailTrace_5765940
  have hstable : (prefixWord ++ tailWord_5765940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765940).length < 2 ^ (prefixWord ++ tailWord_5765940).sum := by decide
  have hdescent : baseEnd_5765940 < baseStart_5765940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765950 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_5765950 : Nat := 118140960795 + 5765950 * 2 ^ 59
def prefixEnd_5765950 : Nat := 4983230072969 + 3 ^ 40 * 5765950 * 2
def baseEnd_5765950 : Nat := 2960703779791820927807885

theorem tailTrace_5765950 : CollatzResearch.WordTrace tailWord_5765950 prefixEnd_5765950 2960703779791820927807885 := by
  unfold tailWord_5765950
  simp only [CollatzResearch.WordTrace]
  refine ⟨26287684182619421338185913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140200982307303580470324869 26287684182619421338185913)
  ·
    refine ⟨19715763136964566003639435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26287684182619421338185913 19715763136964566003639435)
    ·
      refine ⟨29573644705446849005459153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19715763136964566003639435 29573644705446849005459153)
      ·
        refine ⟨22180233529085136754094365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29573644705446849005459153 22180233529085136754094365)
        ·
          refine ⟨8317587573406926282785387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22180233529085136754094365 8317587573406926282785387)
          ·
            refine ⟨12476381360110389424178081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317587573406926282785387 12476381360110389424178081)
            ·
              refine ⟨9357286020082792068133561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12476381360110389424178081 9357286020082792068133561)
              ·
                refine ⟨7017964515062094051100171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9357286020082792068133561 7017964515062094051100171)
                ·
                  refine ⟨10526946772593141076650257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017964515062094051100171 10526946772593141076650257)
                  ·
                    refine ⟨7895210079444855807487693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10526946772593141076650257 7895210079444855807487693)
                    ·
                      refine ⟨2960703779791820927807885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7895210079444855807487693 2960703779791820927807885)
                      ·
                        rfl

theorem cell23_5765950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_5765950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765950 prefixEnd_5765950 := by exact prefixLift 5765950
  have htrace : WordTrace (prefixWord ++ tailWord_5765950) baseStart_5765950 baseEnd_5765950 := by
    simpa [prefixWord, tailWord_5765950, baseEnd_5765950] using wordTrace_append hprefix tailTrace_5765950
  have hstable : (prefixWord ++ tailWord_5765950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765950).length < 2 ^ (prefixWord ++ tailWord_5765950).sum := by decide
  have hdescent : baseEnd_5765950 < baseStart_5765950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765973 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_5765973 : Nat := 118140960795 + 5765973 * 2 ^ 59
def prefixEnd_5765973 : Nat := 4983230072969 + 3 ^ 40 * 5765973 * 2
def baseEnd_5765973 : Nat := 2960715589846874337820279

theorem tailTrace_5765973 : CollatzResearch.WordTrace tailWord_5765973 prefixEnd_5765973 2960715589846874337820279 := by
  unfold tailWord_5765973
  simp only [CollatzResearch.WordTrace]
  refine ⟨210302312339872045633574573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140201541559914697089049715 210302312339872045633574573)
  ·
    refine ⟨78863367127452017112590465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210302312339872045633574573 78863367127452017112590465)
    ·
      refine ⟨59147525345589012834442849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78863367127452017112590465 59147525345589012834442849)
      ·
        refine ⟨44360644009191759625832137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59147525345589012834442849 44360644009191759625832137)
        ·
          refine ⟨33270483006893819719374103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44360644009191759625832137 33270483006893819719374103)
          ·
            refine ⟨49905724510340729579061155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33270483006893819719374103 49905724510340729579061155)
            ·
              refine ⟨74858586765511094368591733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49905724510340729579061155 74858586765511094368591733)
              ·
                refine ⟨7017992509266665097055475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74858586765511094368591733 7017992509266665097055475)
                ·
                  refine ⟨10526988763899997645583213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017992509266665097055475 10526988763899997645583213)
                  ·
                    refine ⟨3947620786462499117093705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10526988763899997645583213 3947620786462499117093705)
                    ·
                      refine ⟨2960715589846874337820279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3947620786462499117093705 2960715589846874337820279)
                      ·
                        rfl

theorem cell23_5765973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_5765973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765973 prefixEnd_5765973 := by exact prefixLift 5765973
  have htrace : WordTrace (prefixWord ++ tailWord_5765973) baseStart_5765973 baseEnd_5765973 := by
    simpa [prefixWord, tailWord_5765973, baseEnd_5765973] using wordTrace_append hprefix tailTrace_5765973
  have hstable : (prefixWord ++ tailWord_5765973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765973).length < 2 ^ (prefixWord ++ tailWord_5765973).sum := by decide
  have hdescent : baseEnd_5765973 < baseStart_5765973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765999 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_5765999 : Nat := 118140960795 + 5765999 * 2 ^ 59
def prefixEnd_5765999 : Nat := 4983230072969 + 3 ^ 40 * 5765999 * 2
def baseEnd_5765999 : Nat := 2960728940343891236095159

theorem tailTrace_5765999 : CollatzResearch.WordTrace tailWord_5765999 prefixEnd_5765999 2960728940343891236095159 := by
  unfold tailWord_5765999
  simp only [CollatzResearch.WordTrace]
  refine ⟨210303260637777852074021051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140202173758518568049347367 210303260637777852074021051)
  ·
    refine ⟨315454890956666778111031577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210303260637777852074021051 315454890956666778111031577)
    ·
      refine ⟨236591168217500083583273683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315454890956666778111031577 236591168217500083583273683)
      ·
        refine ⟨354886752326250125374910525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236591168217500083583273683 354886752326250125374910525)
        ·
          refine ⟨133082532122343797015591447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354886752326250125374910525 133082532122343797015591447)
          ·
            refine ⟨199623798183515695523387171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133082532122343797015591447 199623798183515695523387171)
            ·
              refine ⟨299435697275273543285080757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199623798183515695523387171 299435697275273543285080757)
              ·
                refine ⟨28072096619556894682976321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 299435697275273543285080757 28072096619556894682976321)
                ·
                  refine ⟨21054072464667671012232241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28072096619556894682976321 21054072464667671012232241)
                  ·
                    refine ⟨15790554348500753259174181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21054072464667671012232241 15790554348500753259174181)
                    ·
                      refine ⟨2960728940343891236095159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15790554348500753259174181 2960728940343891236095159)
                      ·
                        rfl

theorem cell23_5765999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_5765999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765999 prefixEnd_5765999 := by exact prefixLift 5765999
  have htrace : WordTrace (prefixWord ++ tailWord_5765999) baseStart_5765999 baseEnd_5765999 := by
    simpa [prefixWord, tailWord_5765999, baseEnd_5765999] using wordTrace_append hprefix tailTrace_5765999
  have hstable : (prefixWord ++ tailWord_5765999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765999).length < 2 ^ (prefixWord ++ tailWord_5765999).sum := by decide
  have hdescent : baseEnd_5765999 < baseStart_5765999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766059 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 4]
def baseStart_5766059 : Nat := 118140960795 + 5766059 * 2 ^ 59
def prefixEnd_5766059 : Nat := 4983230072969 + 3 ^ 40 * 5766059 * 2
def baseEnd_5766059 : Nat := 2960759749183161001344883

theorem tailTrace_5766059 : CollatzResearch.WordTrace tailWord_5766059 prefixEnd_5766059 2960759749183161001344883 := by
  unfold tailWord_5766059
  simp only [CollatzResearch.WordTrace]
  refine ⟨210305449017560482321205231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140203632678373654880803487 210305449017560482321205231)
  ·
    refine ⟨315458173526340723481807847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210305449017560482321205231 315458173526340723481807847)
    ·
      refine ⟨473187260289511085222711771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315458173526340723481807847 473187260289511085222711771)
      ·
        refine ⟨709780890434266627834067657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473187260289511085222711771 709780890434266627834067657)
        ·
          refine ⟨532335667825699970875550743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709780890434266627834067657 532335667825699970875550743)
          ·
            refine ⟨798503501738549956313326115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532335667825699970875550743 798503501738549956313326115)
            ·
              refine ⟨1197755252607824934469989173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798503501738549956313326115 1197755252607824934469989173)
              ·
                refine ⟨112289554931983587606561485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1197755252607824934469989173 112289554931983587606561485)
                ·
                  refine ⟨42108583099493845352460557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112289554931983587606561485 42108583099493845352460557)
                  ·
                    refine ⟨15790718662310192007172709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42108583099493845352460557 15790718662310192007172709)
                    ·
                      refine ⟨2960759749183161001344883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15790718662310192007172709 2960759749183161001344883)
                      ·
                        rfl

theorem cell23_5766059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 4].length) (baseStart_5766059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766059 prefixEnd_5766059 := by exact prefixLift 5766059
  have htrace : WordTrace (prefixWord ++ tailWord_5766059) baseStart_5766059 baseEnd_5766059 := by
    simpa [prefixWord, tailWord_5766059, baseEnd_5766059] using wordTrace_append hprefix tailTrace_5766059
  have hstable : (prefixWord ++ tailWord_5766059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766059).length < 2 ^ (prefixWord ++ tailWord_5766059).sum := by decide
  have hdescent : baseEnd_5766059 < baseStart_5766059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766073 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 2, 5]
def baseStart_5766073 : Nat := 118140960795 + 5766073 * 2 ^ 59
def prefixEnd_5766073 : Nat := 4983230072969 + 3 ^ 40 * 5766073 * 2
def baseEnd_5766073 : Nat := 986922312637441315523273

theorem tailTrace_5766073 : CollatzResearch.WordTrace tailWord_5766073 prefixEnd_5766073 986922312637441315523273 := by
  unfold tailWord_5766073
  simp only [CollatzResearch.WordTrace]
  refine ⟨210305959639509762712214873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140203973093006508474809915 210305959639509762712214873)
  ·
    refine ⟨157729469729632322034161155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210305959639509762712214873 157729469729632322034161155)
    ·
      refine ⟨236594204594448483051241733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157729469729632322034161155 236594204594448483051241733)
      ·
        refine ⟨44361413361459090572107825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236594204594448483051241733 44361413361459090572107825)
        ·
          refine ⟨33271060021094317929080869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44361413361459090572107825 33271060021094317929080869)
          ·
            refine ⟨6238323753955184611702663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33271060021094317929080869 6238323753955184611702663)
            ·
              refine ⟨9357485630932776917553995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238323753955184611702663 9357485630932776917553995)
              ·
                refine ⟨14036228446399165376330993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9357485630932776917553995 14036228446399165376330993)
                ·
                  refine ⟨10527171334799374032248245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14036228446399165376330993 10527171334799374032248245)
                  ·
                    refine ⟨986922312637441315523273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10527171334799374032248245 986922312637441315523273)
                    ·
                      rfl

theorem cell23_5766073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_5766073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766073 prefixEnd_5766073 := by exact prefixLift 5766073
  have htrace : WordTrace (prefixWord ++ tailWord_5766073) baseStart_5766073 baseEnd_5766073 := by
    simpa [prefixWord, tailWord_5766073, baseEnd_5766073] using wordTrace_append hprefix tailTrace_5766073
  have hstable : (prefixWord ++ tailWord_5766073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766073).length < 2 ^ (prefixWord ++ tailWord_5766073).sum := by decide
  have hdescent : baseEnd_5766073 < baseStart_5766073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766079 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_5766079 : Nat := 118140960795 + 5766079 * 2 ^ 59
def prefixEnd_5766079 : Nat := 4983230072969 + 3 ^ 40 * 5766079 * 2
def baseEnd_5766079 : Nat := 2960770018796250923094791

theorem tailTrace_5766079 : CollatzResearch.WordTrace tailWord_5766079 prefixEnd_5766079 2960770018796250923094791 := by
  unfold tailWord_5766079
  simp only [CollatzResearch.WordTrace]
  refine ⟨210306178477488025736933291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140204118984992017157955527 210306178477488025736933291)
  ·
    refine ⟨315459267716232038605399937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210306178477488025736933291 315459267716232038605399937)
    ·
      refine ⟨236594450787174028954049953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315459267716232038605399937 236594450787174028954049953)
      ·
        refine ⟨177445838090380521715537465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236594450787174028954049953 177445838090380521715537465)
        ·
          refine ⟨133084378567785391286653099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177445838090380521715537465 133084378567785391286653099)
          ·
            refine ⟨199626567851678086929979649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133084378567785391286653099 199626567851678086929979649)
            ·
              refine ⟨149719925888758565197484737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199626567851678086929979649 149719925888758565197484737)
              ·
                refine ⟨112289944416568923898113553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149719925888758565197484737 112289944416568923898113553)
                ·
                  refine ⟨84217458312426692923585165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112289944416568923898113553 84217458312426692923585165)
                  ·
                    refine ⟨31581546867160009846344437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84217458312426692923585165 31581546867160009846344437)
                    ·
                      refine ⟨2960770018796250923094791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31581546867160009846344437 2960770018796250923094791)
                      ·
                        rfl

theorem cell23_5766079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_5766079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766079 prefixEnd_5766079 := by exact prefixLift 5766079
  have htrace : WordTrace (prefixWord ++ tailWord_5766079) baseStart_5766079 baseEnd_5766079 := by
    simpa [prefixWord, tailWord_5766079, baseEnd_5766079] using wordTrace_append hprefix tailTrace_5766079
  have hstable : (prefixWord ++ tailWord_5766079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766079).length < 2 ^ (prefixWord ++ tailWord_5766079).sum := by decide
  have hdescent : baseEnd_5766079 < baseStart_5766079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766096 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 3]
def baseStart_5766096 : Nat := 118140960795 + 5766096 * 2 ^ 59
def prefixEnd_5766096 : Nat := 4983230072969 + 3 ^ 40 * 5766096 * 2
def baseEnd_5766096 : Nat := 2960778747967377356582213

theorem tailTrace_5766096 : CollatzResearch.WordTrace tailWord_5766096 prefixEnd_5766096 2960778747967377356582213 := by
  unfold tailWord_5766096
  simp only [CollatzResearch.WordTrace]
  refine ⟨105153399259213218820151071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140204532345617625093534761 105153399259213218820151071)
  ·
    refine ⟨157730098888819828230226607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105153399259213218820151071 157730098888819828230226607)
    ·
      refine ⟨236595148333229742345339911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157730098888819828230226607 236595148333229742345339911)
      ·
        refine ⟨354892722499844613518009867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236595148333229742345339911 354892722499844613518009867)
        ·
          refine ⟨532339083749766920277014801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354892722499844613518009867 532339083749766920277014801)
          ·
            refine ⟨399254312812325190207761101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532339083749766920277014801 399254312812325190207761101)
            ·
              refine ⟨149720367304621946327910413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399254312812325190207761101 149720367304621946327910413)
              ·
                refine ⟨56145137739233229872966405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149720367304621946327910413 56145137739233229872966405)
                ·
                  refine ⟨10527213326106230601181201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56145137739233229872966405 10527213326106230601181201)
                  ·
                    refine ⟨7895409994579672950885901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10527213326106230601181201 7895409994579672950885901)
                    ·
                      refine ⟨2960778747967377356582213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7895409994579672950885901 2960778747967377356582213)
                      ·
                        rfl

theorem cell23_5766096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_5766096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766096 prefixEnd_5766096 := by exact prefixLift 5766096
  have htrace : WordTrace (prefixWord ++ tailWord_5766096) baseStart_5766096 baseEnd_5766096 := by
    simpa [prefixWord, tailWord_5766096, baseEnd_5766096] using wordTrace_append hprefix tailTrace_5766096
  have hstable : (prefixWord ++ tailWord_5766096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766096).length < 2 ^ (prefixWord ++ tailWord_5766096).sum := by decide
  have hdescent : baseEnd_5766096 < baseStart_5766096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766180 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_5766180 : Nat := 118140960795 + 5766180 * 2 ^ 59
def prefixEnd_5766180 : Nat := 4983230072969 + 3 ^ 40 * 5766180 * 2
def baseEnd_5766180 : Nat := 986940626780785009310609

theorem tailTrace_5766180 : CollatzResearch.WordTrace tailWord_5766180 prefixEnd_5766180 986940626780785009310609 := by
  unfold tailWord_5766180
  simp only [CollatzResearch.WordTrace]
  refine ⟨105154931125061059993179997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140206574833414746657573329 105154931125061059993179997)
  ·
    refine ⟨39433099171897897497442499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105154931125061059993179997 39433099171897897497442499)
    ·
      refine ⟨59149648757846846246163749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39433099171897897497442499 59149648757846846246163749)
      ·
        refine ⟨11090559142096283671155703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59149648757846846246163749 11090559142096283671155703)
        ·
          refine ⟨16635838713144425506733555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11090559142096283671155703 16635838713144425506733555)
          ·
            refine ⟨24953758069716638260100333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16635838713144425506733555 24953758069716638260100333)
            ·
              refine ⟨9357659276143739347537625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24953758069716638260100333 9357659276143739347537625)
              ·
                refine ⟨7018244457107804510653219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9357659276143739347537625 7018244457107804510653219)
                ·
                  refine ⟨10527366685661706765979829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7018244457107804510653219 10527366685661706765979829)
                  ·
                    refine ⟨986940626780785009310609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10527366685661706765979829 986940626780785009310609)
                    ·
                      rfl

theorem cell23_5766180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_5766180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766180 prefixEnd_5766180 := by exact prefixLift 5766180
  have htrace : WordTrace (prefixWord ++ tailWord_5766180) baseStart_5766180 baseEnd_5766180 := by
    simpa [prefixWord, tailWord_5766180, baseEnd_5766180] using wordTrace_append hprefix tailTrace_5766180
  have hstable : (prefixWord ++ tailWord_5766180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766180).length < 2 ^ (prefixWord ++ tailWord_5766180).sum := by decide
  have hdescent : baseEnd_5766180 < baseStart_5766180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766250 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_5766250 : Nat := 118140960795 + 5766250 * 2 ^ 59
def prefixEnd_5766250 : Nat := 4983230072969 + 3 ^ 40 * 5766250 * 2
def baseEnd_5766250 : Nat := 2960857823988169754056505

theorem tailTrace_5766250 : CollatzResearch.WordTrace tailWord_5766250 prefixEnd_5766250 2960857823988169754056505 := by
  unfold tailWord_5766250
  simp only [CollatzResearch.WordTrace]
  refine ⟨52578103839967130485352051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140208276906579014627605469 52578103839967130485352051)
  ·
    refine ⟨78867155759950695728028077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52578103839967130485352051 78867155759950695728028077)
    ·
      refine ⟨29575183409981510898010529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78867155759950695728028077 29575183409981510898010529)
      ·
        refine ⟨22181387557486133173507897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29575183409981510898010529 22181387557486133173507897)
        ·
          refine ⟨16636040668114599880130923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22181387557486133173507897 16636040668114599880130923)
          ·
            refine ⟨24954061002171899820196385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16636040668114599880130923 24954061002171899820196385)
            ·
              refine ⟨18715545751628924865147289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24954061002171899820196385 18715545751628924865147289)
              ·
                refine ⟨14036659313721693648860467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18715545751628924865147289 14036659313721693648860467)
                ·
                  refine ⟨21054988970582540473290701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14036659313721693648860467 21054988970582540473290701)
                  ·
                    refine ⟨7895620863968452677484013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21054988970582540473290701 7895620863968452677484013)
                    ·
                      refine ⟨2960857823988169754056505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7895620863968452677484013 2960857823988169754056505)
                      ·
                        rfl

theorem cell23_5766250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_5766250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766250 prefixEnd_5766250 := by exact prefixLift 5766250
  have htrace : WordTrace (prefixWord ++ tailWord_5766250) baseStart_5766250 baseEnd_5766250 := by
    simpa [prefixWord, tailWord_5766250, baseEnd_5766250] using wordTrace_append hprefix tailTrace_5766250
  have hstable : (prefixWord ++ tailWord_5766250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766250).length < 2 ^ (prefixWord ++ tailWord_5766250).sum := by decide
  have hdescent : baseEnd_5766250 < baseStart_5766250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766254 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_5766254 : Nat := 118140960795 + 5766254 * 2 ^ 59
def prefixEnd_5766254 : Nat := 4983230072969 + 3 ^ 40 * 5766254 * 2
def baseEnd_5766254 : Nat := 2960859877910787738406487

theorem tailTrace_5766254 : CollatzResearch.WordTrace tailWord_5766254 prefixEnd_5766254 2960859877910787738406487 := by
  unfold tailWord_5766254
  simp only [CollatzResearch.WordTrace]
  refine ⟨26289070156481753828069227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140208374167902687083035877 26289070156481753828069227)
  ·
    refine ⟨39433605234722630742103841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26289070156481753828069227 39433605234722630742103841)
    ·
      refine ⟨29575203926041973056577881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39433605234722630742103841 29575203926041973056577881)
      ·
        refine ⟨22181402944531479792433411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29575203926041973056577881 22181402944531479792433411)
        ·
          refine ⟨33272104416797219688650117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22181402944531479792433411 33272104416797219688650117)
          ·
            refine ⟨6238519578149478691621897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33272104416797219688650117 6238519578149478691621897)
            ·
              refine ⟨4678889683612109018716423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6238519578149478691621897 4678889683612109018716423)
              ·
                refine ⟨7018334525418163528074635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678889683612109018716423 7018334525418163528074635)
                ·
                  refine ⟨10527501788127245292111953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7018334525418163528074635 10527501788127245292111953)
                  ·
                    refine ⟨7895626341095433969083965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10527501788127245292111953 7895626341095433969083965)
                    ·
                      refine ⟨2960859877910787738406487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7895626341095433969083965 2960859877910787738406487)
                      ·
                        rfl

theorem cell23_5766254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_5766254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766254 prefixEnd_5766254 := by exact prefixLift 5766254
  have htrace : WordTrace (prefixWord ++ tailWord_5766254) baseStart_5766254 baseEnd_5766254 := by
    simpa [prefixWord, tailWord_5766254, baseEnd_5766254] using wordTrace_append hprefix tailTrace_5766254
  have hstable : (prefixWord ++ tailWord_5766254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766254).length < 2 ^ (prefixWord ++ tailWord_5766254).sum := by decide
  have hdescent : baseEnd_5766254 < baseStart_5766254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766261 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_5766261 : Nat := 118140960795 + 5766261 * 2 ^ 59
def prefixEnd_5766261 : Nat := 4983230072969 + 3 ^ 40 * 5766261 * 2
def baseEnd_5766261 : Nat := 986954490758456403672985

theorem tailTrace_5766261 : CollatzResearch.WordTrace tailWord_5766261 prefixEnd_5766261 986954490758456403672985 := by
  unfold tailWord_5766261
  simp only [CollatzResearch.WordTrace]
  refine ⟨210312816562828670820058637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140208544375219113880039091 210312816562828670820058637)
  ·
    refine ⟨78867306211060751557521989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210312816562828670820058637 78867306211060751557521989)
    ·
      refine ⟨14787619914573890917035373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78867306211060751557521989 14787619914573890917035373)
      ·
        refine ⟨5545357467965209093888265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14787619914573890917035373 5545357467965209093888265)
        ·
          refine ⟨4159018100973906820416199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5545357467965209093888265 4159018100973906820416199)
          ·
            refine ⟨6238527151460860230624299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159018100973906820416199 6238527151460860230624299)
            ·
              refine ⟨9357790727191290345936449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238527151460860230624299 9357790727191290345936449)
              ·
                refine ⟨7018343045393467759452337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9357790727191290345936449 7018343045393467759452337)
                ·
                  refine ⟨5263757284045100819589253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7018343045393467759452337 5263757284045100819589253)
                  ·
                    refine ⟨986954490758456403672985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5263757284045100819589253 986954490758456403672985)
                    ·
                      rfl

theorem cell23_5766261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_5766261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766261 prefixEnd_5766261 := by exact prefixLift 5766261
  have htrace : WordTrace (prefixWord ++ tailWord_5766261) baseStart_5766261 baseEnd_5766261 := by
    simpa [prefixWord, tailWord_5766261, baseEnd_5766261] using wordTrace_append hprefix tailTrace_5766261
  have hstable : (prefixWord ++ tailWord_5766261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766261).length < 2 ^ (prefixWord ++ tailWord_5766261).sum := by decide
  have hdescent : baseEnd_5766261 < baseStart_5766261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766323 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 3]
def baseStart_5766323 : Nat := 118140960795 + 5766323 * 2 ^ 59
def prefixEnd_5766323 : Nat := 4983230072969 + 3 ^ 40 * 5766323 * 2
def baseEnd_5766323 : Nat := 2960895308075947968443669

theorem tailTrace_5766323 : CollatzResearch.WordTrace tailWord_5766323 prefixEnd_5766323 2960895308075947968443669 := by
  unfold tailWord_5766323
  simp only [CollatzResearch.WordTrace]
  refine ⟨210315077888604055408815623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140210051925736036939210415 210315077888604055408815623)
  ·
    refine ⟨315472616832906083113223435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210315077888604055408815623 315472616832906083113223435)
    ·
      refine ⟨473208925249359124669835153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315472616832906083113223435 473208925249359124669835153)
      ·
        refine ⟨354906693937019343502376365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473208925249359124669835153 354906693937019343502376365)
        ·
          refine ⟨133090010226382253813391137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354906693937019343502376365 133090010226382253813391137)
          ·
            refine ⟨99817507669786690360043353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133090010226382253813391137 99817507669786690360043353)
            ·
              refine ⟨74863130752340017770032515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99817507669786690360043353 74863130752340017770032515)
              ·
                refine ⟨112294696128510026655048773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74863130752340017770032515 112294696128510026655048773)
                ·
                  refine ⟨21055255524095629997821645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112294696128510026655048773 21055255524095629997821645)
                  ·
                    refine ⟨7895720821535861249183117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21055255524095629997821645 7895720821535861249183117)
                    ·
                      refine ⟨2960895308075947968443669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7895720821535861249183117 2960895308075947968443669)
                      ·
                        rfl

theorem cell23_5766323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_5766323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766323 prefixEnd_5766323 := by exact prefixLift 5766323
  have htrace : WordTrace (prefixWord ++ tailWord_5766323) baseStart_5766323 baseEnd_5766323 := by
    simpa [prefixWord, tailWord_5766323, baseEnd_5766323] using wordTrace_append hprefix tailTrace_5766323
  have hstable : (prefixWord ++ tailWord_5766323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766323).length < 2 ^ (prefixWord ++ tailWord_5766323).sum := by decide
  have hdescent : baseEnd_5766323 < baseStart_5766323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766380 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_5766380 : Nat := 118140960795 + 5766380 * 2 ^ 59
def prefixEnd_5766380 : Nat := 4983230072969 + 3 ^ 40 * 5766380 * 2
def baseEnd_5766380 : Nat := 2960924576473254245430907

theorem tailTrace_5766380 : CollatzResearch.WordTrace tailWord_5766380 prefixEnd_5766380 2960924576473254245430907 := by
  unfold tailWord_5766380
  simp only [CollatzResearch.WordTrace]
  refine ⟨105158578424698777071820297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140211437899598369429093729 105158578424698777071820297)
  ·
    refine ⟨78868933818524082803865223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105158578424698777071820297 78868933818524082803865223)
    ·
      refine ⟨118303400727786124205797835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78868933818524082803865223 118303400727786124205797835)
      ·
        refine ⟨177455101091679186308696753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118303400727786124205797835 177455101091679186308696753)
        ·
          refine ⟨133091325818759389731522565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177455101091679186308696753 133091325818759389731522565)
          ·
            refine ⟨24954623591017385574660481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133091325818759389731522565 24954623591017385574660481)
            ·
              refine ⟨18715967693263039180995361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24954623591017385574660481 18715967693263039180995361)
              ·
                refine ⟨14036975769947279385746521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18715967693263039180995361 14036975769947279385746521)
                ·
                  refine ⟨10527731827460459539309891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14036975769947279385746521 10527731827460459539309891)
                  ·
                    refine ⟨15791597741190689308964837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10527731827460459539309891 15791597741190689308964837)
                    ·
                      refine ⟨2960924576473254245430907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15791597741190689308964837 2960924576473254245430907)
                      ·
                        rfl

theorem cell23_5766380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_5766380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766380 prefixEnd_5766380 := by exact prefixLift 5766380
  have htrace : WordTrace (prefixWord ++ tailWord_5766380) baseStart_5766380 baseEnd_5766380 := by
    simpa [prefixWord, tailWord_5766380, baseEnd_5766380] using wordTrace_append hprefix tailTrace_5766380
  have hstable : (prefixWord ++ tailWord_5766380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766380).length < 2 ^ (prefixWord ++ tailWord_5766380).sum := by decide
  have hdescent : baseEnd_5766380 < baseStart_5766380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766424 : List Nat := [2, 1, 2, 3, 1, 4, 2, 3, 1, 4]
def baseStart_5766424 : Nat := 118140960795 + 5766424 * 2 ^ 59
def prefixEnd_5766424 : Nat := 4983230072969 + 3 ^ 40 * 5766424 * 2
def baseEnd_5766424 : Nat := 986982389874017357760235

theorem tailTrace_5766424 : CollatzResearch.WordTrace tailWord_5766424 prefixEnd_5766424 986982389874017357760235 := by
  unfold tailWord_5766424
  simp only [CollatzResearch.WordTrace]
  refine ⟨105159380830619074829121163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140212507774158766438828217 105159380830619074829121163)
  ·
    refine ⟨157739071245928612243681745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105159380830619074829121163 157739071245928612243681745)
    ·
      refine ⟨118304303434446459182761309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157739071245928612243681745 118304303434446459182761309)
      ·
        refine ⟨44364113787917422193535491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118304303434446459182761309 44364113787917422193535491)
        ·
          refine ⟨66546170681876133290303237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44364113787917422193535491 66546170681876133290303237)
          ·
            refine ⟨12477407002851774991931857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66546170681876133290303237 12477407002851774991931857)
            ·
              refine ⟨9358055252138831243948893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12477407002851774991931857 9358055252138831243948893)
              ·
                refine ⟨3509270719552061716480835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9358055252138831243948893 3509270719552061716480835)
                ·
                  refine ⟨5263906079328092574721253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509270719552061716480835 5263906079328092574721253)
                  ·
                    refine ⟨986982389874017357760235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5263906079328092574721253 986982389874017357760235)
                    ·
                      rfl

theorem cell23_5766424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_5766424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766424 prefixEnd_5766424 := by exact prefixLift 5766424
  have htrace : WordTrace (prefixWord ++ tailWord_5766424) baseStart_5766424 baseEnd_5766424 := by
    simpa [prefixWord, tailWord_5766424, baseEnd_5766424] using wordTrace_append hprefix tailTrace_5766424
  have hstable : (prefixWord ++ tailWord_5766424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766424).length < 2 ^ (prefixWord ++ tailWord_5766424).sum := by decide
  have hdescent : baseEnd_5766424 < baseStart_5766424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766437 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 6]
def baseStart_5766437 : Nat := 118140960795 + 5766437 * 2 ^ 59
def prefixEnd_5766437 : Nat := 4983230072969 + 3 ^ 40 * 5766437 * 2
def baseEnd_5766437 : Nat := 328994871652284502490905

theorem tailTrace_5766437 : CollatzResearch.WordTrace tailWord_5766437 prefixEnd_5766437 328994871652284502490905 := by
  unfold tailWord_5766437
  simp only [CollatzResearch.WordTrace]
  refine ⟨210319235810191052878465565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140212823873460701918977043 210319235810191052878465565)
  ·
    refine ⟨78869713428821644829424587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210319235810191052878465565 78869713428821644829424587)
    ·
      refine ⟨118304570143232467244136881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78869713428821644829424587 118304570143232467244136881)
      ·
        refine ⟨88728427607424350433102661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118304570143232467244136881 88728427607424350433102661)
        ·
          refine ⟨16636580176392065706206749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88728427607424350433102661 16636580176392065706206749)
          ·
            refine ⟨6238717566147024639827531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16636580176392065706206749 6238717566147024639827531)
            ·
              refine ⟨9358076349220536959741297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238717566147024639827531 9358076349220536959741297)
              ·
                refine ⟨7018557261915402719805973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9358076349220536959741297 7018557261915402719805973)
                ·
                  refine ⟨328994871652284502490905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7018557261915402719805973 328994871652284502490905)
                  ·
                    rfl

theorem cell23_5766437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_5766437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766437 prefixEnd_5766437 := by exact prefixLift 5766437
  have htrace : WordTrace (prefixWord ++ tailWord_5766437) baseStart_5766437 baseEnd_5766437 := by
    simpa [prefixWord, tailWord_5766437, baseEnd_5766437] using wordTrace_append hprefix tailTrace_5766437
  have hstable : (prefixWord ++ tailWord_5766437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766437).length < 2 ^ (prefixWord ++ tailWord_5766437).sum := by decide
  have hdescent : baseEnd_5766437 < baseStart_5766437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766440 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5766440 : Nat := 118140960795 + 5766440 * 2 ^ 59
def prefixEnd_5766440 : Nat := 4983230072969 + 3 ^ 40 * 5766440 * 2
def baseEnd_5766440 : Nat := 2960955385312524010680631

theorem tailTrace_5766440 : CollatzResearch.WordTrace tailWord_5766440 prefixEnd_5766440 2960955385312524010680631 := by
  unfold tailWord_5766440
  simp only [CollatzResearch.WordTrace]
  refine ⟨105159672614590092195412387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140212896819453456260549849 105159672614590092195412387)
  ·
    refine ⟨157739508921885138293118581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105159672614590092195412387 157739508921885138293118581)
    ·
      refine ⟨14788078961426731714979867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157739508921885138293118581 14788078961426731714979867)
      ·
        refine ⟨22182118442140097572469801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14788078961426731714979867 22182118442140097572469801)
        ·
          refine ⟨16636588831605073179352351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22182118442140097572469801 16636588831605073179352351)
          ·
            refine ⟨24954883247407609769028527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16636588831605073179352351 24954883247407609769028527)
            ·
              refine ⟨37432324871111414653542791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24954883247407609769028527 37432324871111414653542791)
              ·
                refine ⟨56148487306667121980314187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37432324871111414653542791 56148487306667121980314187)
                ·
                  refine ⟨84222730960000682970471281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56148487306667121980314187 84222730960000682970471281)
                  ·
                    refine ⟨63167048220000512227853461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84222730960000682970471281 63167048220000512227853461)
                    ·
                      refine ⟨2960955385312524010680631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63167048220000512227853461 2960955385312524010680631)
                      ·
                        rfl

theorem cell23_5766440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5766440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766440 prefixEnd_5766440 := by exact prefixLift 5766440
  have htrace : WordTrace (prefixWord ++ tailWord_5766440) baseStart_5766440 baseEnd_5766440 := by
    simpa [prefixWord, tailWord_5766440, baseEnd_5766440] using wordTrace_append hprefix tailTrace_5766440
  have hstable : (prefixWord ++ tailWord_5766440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766440).length < 2 ^ (prefixWord ++ tailWord_5766440).sum := by decide
  have hdescent : baseEnd_5766440 < baseStart_5766440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766480 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 6, 4]
def baseStart_5766480 : Nat := 118140960795 + 5766480 * 2 ^ 59
def prefixEnd_5766480 : Nat := 4983230072969 + 3 ^ 40 * 5766480 * 2
def baseEnd_5766480 : Nat := 986991974846234618060149

theorem tailTrace_5766480 : CollatzResearch.WordTrace tailWord_5766480 prefixEnd_5766480 986991974846234618060149 := by
  unfold tailWord_5766480
  simp only [CollatzResearch.WordTrace]
  refine ⟨105160402074517635611140447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140213869432690180814853929 105160402074517635611140447)
  ·
    refine ⟨157740603111776453416710671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105160402074517635611140447 157740603111776453416710671)
    ·
      refine ⟨236610904667664680125066007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157740603111776453416710671 236610904667664680125066007)
      ·
        refine ⟨354916357001497020187599011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236610904667664680125066007 354916357001497020187599011)
        ·
          refine ⟨532374535502245530281398517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354916357001497020187599011 532374535502245530281398517)
          ·
            refine ⟨49910112703335518463881111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 532374535502245530281398517 49910112703335518463881111)
            ·
              refine ⟨74865169055003277695821667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49910112703335518463881111 74865169055003277695821667)
              ·
                refine ⟨112297753582504916543732501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74865169055003277695821667 112297753582504916543732501)
                ·
                  refine ⟨5263957199179917962987461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112297753582504916543732501 5263957199179917962987461)
                  ·
                    refine ⟨986991974846234618060149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5263957199179917962987461 986991974846234618060149)
                    ·
                      rfl

theorem cell23_5766480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 4].length) (baseStart_5766480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766480 prefixEnd_5766480 := by exact prefixLift 5766480
  have htrace : WordTrace (prefixWord ++ tailWord_5766480) baseStart_5766480 baseEnd_5766480 := by
    simpa [prefixWord, tailWord_5766480, baseEnd_5766480] using wordTrace_append hprefix tailTrace_5766480
  have hstable : (prefixWord ++ tailWord_5766480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766480).length < 2 ^ (prefixWord ++ tailWord_5766480).sum := by decide
  have hdescent : baseEnd_5766480 < baseStart_5766480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766487 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_5766487 : Nat := 118140960795 + 5766487 * 2 ^ 59
def prefixEnd_5766487 : Nat := 4983230072969 + 3 ^ 40 * 5766487 * 2
def baseEnd_5766487 : Nat := 2960979518903285326792915

theorem tailTrace_5766487 : CollatzResearch.WordTrace tailWord_5766487 prefixEnd_5766487 2960979518903285326792915 := by
  unfold tailWord_5766487
  simp only [CollatzResearch.WordTrace]
  refine ⟨210321059460009911417785715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140214039640006607611857143 210321059460009911417785715)
  ·
    refine ⟨315481589190014867126678573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210321059460009911417785715 315481589190014867126678573)
    ·
      refine ⟨118305595946255575172504465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315481589190014867126678573 118305595946255575172504465)
      ·
        refine ⟨88729196959691681379378349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118305595946255575172504465 88729196959691681379378349)
        ·
          refine ⟨33273448859884380517266881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88729196959691681379378349 33273448859884380517266881)
          ·
            refine ⟨24955086644913285387950161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33273448859884380517266881 24955086644913285387950161)
            ·
              refine ⟨18716314983684964040962621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24955086644913285387950161 18716314983684964040962621)
              ·
                refine ⟨7018618118881861515360983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18716314983684964040962621 7018618118881861515360983)
                ·
                  refine ⟨10527927178322792273041475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7018618118881861515360983 10527927178322792273041475)
                  ·
                    refine ⟨15791890767484188409562213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10527927178322792273041475 15791890767484188409562213)
                    ·
                      refine ⟨2960979518903285326792915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15791890767484188409562213 2960979518903285326792915)
                      ·
                        rfl

theorem cell23_5766487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_5766487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766487 prefixEnd_5766487 := by exact prefixLift 5766487
  have htrace : WordTrace (prefixWord ++ tailWord_5766487) baseStart_5766487 baseEnd_5766487 := by
    simpa [prefixWord, tailWord_5766487, baseEnd_5766487] using wordTrace_append hprefix tailTrace_5766487
  have hstable : (prefixWord ++ tailWord_5766487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766487).length < 2 ^ (prefixWord ++ tailWord_5766487).sum := by decide
  have hdescent : baseEnd_5766487 < baseStart_5766487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766490 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_5766490 : Nat := 118140960795 + 5766490 * 2 ^ 59
def prefixEnd_5766490 : Nat := 4983230072969 + 3 ^ 40 * 5766490 * 2
def baseEnd_5766490 : Nat := 2960981059345248815055401

theorem tailTrace_5766490 : CollatzResearch.WordTrace tailWord_5766490 prefixEnd_5766490 2960981059345248815055401 := by
  unfold tailWord_5766490
  simp only [CollatzResearch.WordTrace]
  refine ⟨52580292219749760732536231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140214112585999361953429949 52580292219749760732536231)
  ·
    refine ⟨78870438329624641098804347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52580292219749760732536231 78870438329624641098804347)
    ·
      refine ⟨118305657494436961648206521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78870438329624641098804347 118305657494436961648206521)
      ·
        refine ⟨88729243120827721236154891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118305657494436961648206521 88729243120827721236154891)
        ·
          refine ⟨133093864681241581854232337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88729243120827721236154891 133093864681241581854232337)
          ·
            refine ⟨99820398510931186390674253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133093864681241581854232337 99820398510931186390674253)
            ·
              refine ⟨37432649441599194896502845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99820398510931186390674253 37432649441599194896502845)
              ·
                refine ⟨14037243540599698086188567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37432649441599194896502845 14037243540599698086188567)
                ·
                  refine ⟨21055865310899547129282851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14037243540599698086188567 21055865310899547129282851)
                  ·
                    refine ⟨31583797966349320693924277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21055865310899547129282851 31583797966349320693924277)
                    ·
                      refine ⟨2960981059345248815055401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31583797966349320693924277 2960981059345248815055401)
                      ·
                        rfl

theorem cell23_5766490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_5766490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766490 prefixEnd_5766490 := by exact prefixLift 5766490
  have htrace : WordTrace (prefixWord ++ tailWord_5766490) baseStart_5766490 baseEnd_5766490 := by
    simpa [prefixWord, tailWord_5766490, baseEnd_5766490] using wordTrace_append hprefix tailTrace_5766490
  have hstable : (prefixWord ++ tailWord_5766490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766490).length < 2 ^ (prefixWord ++ tailWord_5766490).sum := by decide
  have hdescent : baseEnd_5766490 < baseStart_5766490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766498 : List Nat := [3, 3, 2, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_5766498 : Nat := 118140960795 + 5766498 * 2 ^ 59
def prefixEnd_5766498 : Nat := 4983230072969 + 3 ^ 40 * 5766498 * 2
def baseEnd_5766498 : Nat := 2960985167190484783755365

theorem tailTrace_5766498 : CollatzResearch.WordTrace tailWord_5766498 prefixEnd_5766498 2960985167190484783755365 := by
  unfold tailWord_5766498
  simp only [CollatzResearch.WordTrace]
  refine ⟨52580365165742515074109037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140214307108646706864290765 52580365165742515074109037)
  ·
    refine ⟨19717636937153443152790889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52580365165742515074109037 19717636937153443152790889)
    ·
      refine ⟨14788227702865082364593167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19717636937153443152790889 14788227702865082364593167)
      ·
        refine ⟨22182341554297623546889751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14788227702865082364593167 22182341554297623546889751)
        ·
          refine ⟨33273512331446435320334627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22182341554297623546889751 33273512331446435320334627)
          ·
            refine ⟨49910268497169652980501941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33273512331446435320334627 49910268497169652980501941)
            ·
              refine ⟨4679087671609654966922057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49910268497169652980501941 4679087671609654966922057)
              ·
                refine ⟨3509315753707241225191543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4679087671609654966922057 3509315753707241225191543)
                ·
                  refine ⟨5263973630560861837787315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509315753707241225191543 5263973630560861837787315)
                  ·
                    refine ⟨7895960445841292756680973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5263973630560861837787315 7895960445841292756680973)
                    ·
                      refine ⟨2960985167190484783755365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7895960445841292756680973 2960985167190484783755365)
                      ·
                        rfl

theorem cell23_5766498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_5766498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766498 prefixEnd_5766498 := by exact prefixLift 5766498
  have htrace : WordTrace (prefixWord ++ tailWord_5766498) baseStart_5766498 baseEnd_5766498 := by
    simpa [prefixWord, tailWord_5766498, baseEnd_5766498] using wordTrace_append hprefix tailTrace_5766498
  have hstable : (prefixWord ++ tailWord_5766498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766498).length < 2 ^ (prefixWord ++ tailWord_5766498).sum := by decide
  have hdescent : baseEnd_5766498 < baseStart_5766498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766500 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_5766500 : Nat := 118140960795 + 5766500 * 2 ^ 59
def prefixEnd_5766500 : Nat := 4983230072969 + 3 ^ 40 * 5766500 * 2
def baseEnd_5766500 : Nat := 2960986194151793775930355

theorem tailTrace_5766500 : CollatzResearch.WordTrace tailWord_5766500 prefixEnd_5766500 2960986194151793775930355 := by
  unfold tailWord_5766500
  simp only [CollatzResearch.WordTrace]
  refine ⟨105160766804481407319004477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140214355739308543092005969 105160766804481407319004477)
  ·
    refine ⟨39435287551680527744626679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105160766804481407319004477 39435287551680527744626679)
    ·
      refine ⟨59152931327520791616940019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39435287551680527744626679 59152931327520791616940019)
      ·
        refine ⟨88729396991281187425410029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59152931327520791616940019 88729396991281187425410029)
        ·
          refine ⟨33273523871730445284528761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88729396991281187425410029 33273523871730445284528761)
          ·
            refine ⟨24955142903797833963396571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33273523871730445284528761 24955142903797833963396571)
            ·
              refine ⟨37432714355696750945094857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24955142903797833963396571 37432714355696750945094857)
              ·
                refine ⟨28074535766772563208821143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37432714355696750945094857 28074535766772563208821143)
                ·
                  refine ⟨42111803650158844813231715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28074535766772563208821143 42111803650158844813231715)
                  ·
                    refine ⟨63167705475238267219847573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42111803650158844813231715 63167705475238267219847573)
                    ·
                      refine ⟨2960986194151793775930355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63167705475238267219847573 2960986194151793775930355)
                      ·
                        rfl

theorem cell23_5766500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_5766500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766500 prefixEnd_5766500 := by exact prefixLift 5766500
  have htrace : WordTrace (prefixWord ++ tailWord_5766500) baseStart_5766500 baseEnd_5766500 := by
    simpa [prefixWord, tailWord_5766500, baseEnd_5766500] using wordTrace_append hprefix tailTrace_5766500
  have hstable : (prefixWord ++ tailWord_5766500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766500).length < 2 ^ (prefixWord ++ tailWord_5766500).sum := by decide
  have hdescent : baseEnd_5766500 < baseStart_5766500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766520 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_5766520 : Nat := 118140960795 + 5766520 * 2 ^ 59
def prefixEnd_5766520 : Nat := 4983230072969 + 3 ^ 40 * 5766520 * 2
def baseEnd_5766520 : Nat := 2960996463764883697680263

theorem tailTrace_5766520 : CollatzResearch.WordTrace tailWord_5766520 prefixEnd_5766520 2960996463764883697680263 := by
  unfold tailWord_5766520
  simp only [CollatzResearch.WordTrace]
  refine ⟨105161131534445179026868507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140214842045926905369158009 105161131534445179026868507)
  ·
    refine ⟨157741697301667768540302761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105161131534445179026868507 157741697301667768540302761)
    ·
      refine ⟨118306272976250826405227071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157741697301667768540302761 118306272976250826405227071)
      ·
        refine ⟨177459409464376239607840607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118306272976250826405227071 177459409464376239607840607)
        ·
          refine ⟨266189114196564359411760911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177459409464376239607840607 266189114196564359411760911)
          ·
            refine ⟨399283671294846539117641367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266189114196564359411760911 399283671294846539117641367)
            ·
              refine ⟨598925506942269808676462051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399283671294846539117641367 598925506942269808676462051)
              ·
                refine ⟨898388260413404713014693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598925506942269808676462051 898388260413404713014693077)
                ·
                  refine ⟨21055974853439172961281869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 898388260413404713014693077 21055974853439172961281869)
                  ·
                    refine ⟨7895990570039689860480701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21055974853439172961281869 7895990570039689860480701)
                    ·
                      refine ⟨2960996463764883697680263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7895990570039689860480701 2960996463764883697680263)
                      ·
                        rfl

theorem cell23_5766520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_5766520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766520 prefixEnd_5766520 := by exact prefixLift 5766520
  have htrace : WordTrace (prefixWord ++ tailWord_5766520) baseStart_5766520 baseEnd_5766520 := by
    simpa [prefixWord, tailWord_5766520, baseEnd_5766520] using wordTrace_append hprefix tailTrace_5766520
  have hstable : (prefixWord ++ tailWord_5766520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766520).length < 2 ^ (prefixWord ++ tailWord_5766520).sum := by decide
  have hdescent : baseEnd_5766520 < baseStart_5766520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766560 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_5766560 : Nat := 118140960795 + 5766560 * 2 ^ 59
def prefixEnd_5766560 : Nat := 4983230072969 + 3 ^ 40 * 5766560 * 2
def baseEnd_5766560 : Nat := 2961017002991063541180079

theorem tailTrace_5766560 : CollatzResearch.WordTrace tailWord_5766560 prefixEnd_5766560 2961017002991063541180079 := by
  unfold tailWord_5766560
  simp only [CollatzResearch.WordTrace]
  refine ⟨105161860994372722442596567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140215814659163629923462089 105161860994372722442596567)
  ·
    refine ⟨157742791491559083663894851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105161860994372722442596567 157742791491559083663894851)
    ·
      refine ⟨236614187237338625495842277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157742791491559083663894851 236614187237338625495842277)
      ·
        refine ⟨44365160107000992280470427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236614187237338625495842277 44365160107000992280470427)
        ·
          refine ⟨66547740160501488420705641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44365160107000992280470427 66547740160501488420705641)
          ·
            refine ⟨49910805120376116315529231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66547740160501488420705641 49910805120376116315529231)
            ·
              refine ⟨74866207680564174473293847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49910805120376116315529231 74866207680564174473293847)
              ·
                refine ⟨112299311520846261709940771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74866207680564174473293847 112299311520846261709940771)
                ·
                  refine ⟨168448967281269392564911157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112299311520846261709940771 168448967281269392564911157)
                  ·
                    refine ⟨15792090682619005552960421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 168448967281269392564911157 15792090682619005552960421)
                    ·
                      refine ⟨2961017002991063541180079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15792090682619005552960421 2961017002991063541180079)
                      ·
                        rfl

theorem cell23_5766560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_5766560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766560 prefixEnd_5766560 := by exact prefixLift 5766560
  have htrace : WordTrace (prefixWord ++ tailWord_5766560) baseStart_5766560 baseEnd_5766560 := by
    simpa [prefixWord, tailWord_5766560, baseEnd_5766560] using wordTrace_append hprefix tailTrace_5766560
  have hstable : (prefixWord ++ tailWord_5766560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766560).length < 2 ^ (prefixWord ++ tailWord_5766560).sum := by decide
  have hdescent : baseEnd_5766560 < baseStart_5766560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766600 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 9]
def baseStart_5766600 : Nat := 118140960795 + 5766600 * 2 ^ 59
def prefixEnd_5766600 : Nat := 4983230072969 + 3 ^ 40 * 5766600 * 2
def baseEnd_5766600 : Nat := 329004171357471487186655

theorem tailTrace_5766600 : CollatzResearch.WordTrace tailWord_5766600 prefixEnd_5766600 329004171357471487186655 := by
  unfold tailWord_5766600
  simp only [CollatzResearch.WordTrace]
  refine ⟨105162590454300265858324627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140216787272400354477766169 105162590454300265858324627)
  ·
    refine ⟨157743885681450398787486941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105162590454300265858324627 157743885681450398787486941)
    ·
      refine ⟨59153957130543899545307603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157743885681450398787486941 59153957130543899545307603)
      ·
        refine ⟨88730935695815849317961405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59153957130543899545307603 88730935695815849317961405)
        ·
          refine ⟨33274100885930943494235527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88730935695815849317961405 33274100885930943494235527)
          ·
            refine ⟨49911151328896415241353291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33274100885930943494235527 49911151328896415241353291)
            ·
              refine ⟨74866726993344622862029937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49911151328896415241353291 74866726993344622862029937)
              ·
                refine ⟨56150045245008467146522453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74866726993344622862029937 56150045245008467146522453)
                ·
                  refine ⟨329004171357471487186655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56150045245008467146522453 329004171357471487186655)
                  ·
                    rfl

theorem cell23_5766600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 9].length) (baseStart_5766600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766600 prefixEnd_5766600 := by exact prefixLift 5766600
  have htrace : WordTrace (prefixWord ++ tailWord_5766600) baseStart_5766600 baseEnd_5766600 := by
    simpa [prefixWord, tailWord_5766600, baseEnd_5766600] using wordTrace_append hprefix tailTrace_5766600
  have hstable : (prefixWord ++ tailWord_5766600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766600).length < 2 ^ (prefixWord ++ tailWord_5766600).sum := by decide
  have hdescent : baseEnd_5766600 < baseStart_5766600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766617 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 7]
def baseStart_5766617 : Nat := 118140960795 + 5766617 * 2 ^ 59
def prefixEnd_5766617 : Nat := 4983230072969 + 3 ^ 40 * 5766617 * 2
def baseEnd_5766617 : Nat := 329005141265374424240813

theorem tailTrace_5766617 : CollatzResearch.WordTrace tailWord_5766617 prefixEnd_5766617 329005141265374424240813 := by
  unfold tailWord_5766617
  simp only [CollatzResearch.WordTrace]
  refine ⟨210325800949538943620018105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140217200633025962413345403 210325800949538943620018105)
  ·
    refine ⟨157744350712154207715013579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210325800949538943620018105 157744350712154207715013579)
    ·
      refine ⟨236616526068231311572520369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157744350712154207715013579 236616526068231311572520369)
      ·
        refine ⟨177462394551173483679390277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236616526068231311572520369 177462394551173483679390277)
        ·
          refine ⟨33274198978345028189885677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177462394551173483679390277 33274198978345028189885677)
          ·
            refine ⟨12477824616879385571207129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33274198978345028189885677 12477824616879385571207129)
            ·
              refine ⟨9358368462659539178405347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12477824616879385571207129 9358368462659539178405347)
              ·
                refine ⟨14037552693989308767608021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9358368462659539178405347 14037552693989308767608021)
                ·
                  refine ⟨329005141265374424240813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14037552693989308767608021 329005141265374424240813)
                  ·
                    rfl

theorem cell23_5766617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 7].length) (baseStart_5766617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766617 prefixEnd_5766617 := by exact prefixLift 5766617
  have htrace : WordTrace (prefixWord ++ tailWord_5766617) baseStart_5766617 baseEnd_5766617 := by
    simpa [prefixWord, tailWord_5766617, baseEnd_5766617] using wordTrace_append hprefix tailTrace_5766617
  have hstable : (prefixWord ++ tailWord_5766617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766617).length < 2 ^ (prefixWord ++ tailWord_5766617).sum := by decide
  have hdescent : baseEnd_5766617 < baseStart_5766617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766684 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_5766684 : Nat := 118140960795 + 5766684 * 2 ^ 59
def prefixEnd_5766684 : Nat := 4983230072969 + 3 ^ 40 * 5766684 * 2
def baseEnd_5766684 : Nat := 2961080674592221056029509

theorem tailTrace_5766684 : CollatzResearch.WordTrace tailWord_5766684 prefixEnd_5766684 2961080674592221056029509 := by
  unfold tailWord_5766684
  simp only [CollatzResearch.WordTrace]
  refine ⟨105164122320148107031353553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140218829760197476041804737 105164122320148107031353553)
  ·
    refine ⟨78873091740111080273515165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105164122320148107031353553 78873091740111080273515165)
    ·
      refine ⟨29577409402541655102568187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78873091740111080273515165 29577409402541655102568187)
      ·
        refine ⟨44366114103812482653852281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29577409402541655102568187 44366114103812482653852281)
        ·
          refine ⟨33274585577859361990389211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44366114103812482653852281 33274585577859361990389211)
          ·
            refine ⟨49911878366789042985583817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33274585577859361990389211 49911878366789042985583817)
            ·
              refine ⟨37433908775091782239187863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49911878366789042985583817 37433908775091782239187863)
              ·
                refine ⟨56150863162637673358781795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37433908775091782239187863 56150863162637673358781795)
                ·
                  refine ⟨84226294743956510038172693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56150863162637673358781795 84226294743956510038172693)
                  ·
                    refine ⟨3948107566122961408039345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84226294743956510038172693 3948107566122961408039345)
                    ·
                      refine ⟨2961080674592221056029509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948107566122961408039345 2961080674592221056029509)
                      ·
                        rfl

theorem cell23_5766684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_5766684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766684 prefixEnd_5766684 := by exact prefixLift 5766684
  have htrace : WordTrace (prefixWord ++ tailWord_5766684) baseStart_5766684 baseEnd_5766684 := by
    simpa [prefixWord, tailWord_5766684, baseEnd_5766684] using wordTrace_append hprefix tailTrace_5766684
  have hstable : (prefixWord ++ tailWord_5766684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766684).length < 2 ^ (prefixWord ++ tailWord_5766684).sum := by decide
  have hdescent : baseEnd_5766684 < baseStart_5766684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766687 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 3]
def baseStart_5766687 : Nat := 118140960795 + 5766687 * 2 ^ 59
def prefixEnd_5766687 : Nat := 4983230072969 + 3 ^ 40 * 5766687 * 2
def baseEnd_5766687 : Nat := 2961082215034184544291995

theorem tailTrace_5766687 : CollatzResearch.WordTrace tailWord_5766687 prefixEnd_5766687 2961082215034184544291995 := by
  unfold tailWord_5766687
  simp only [CollatzResearch.WordTrace]
  refine ⟨210328354059285345575066315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140218902706190230383377543 210328354059285345575066315)
  ·
    refine ⟨315492531088928018362599473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210328354059285345575066315 315492531088928018362599473)
    ·
      refine ⟨236619398316696013771949605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315492531088928018362599473 236619398316696013771949605)
      ·
        refine ⟨44366137184380502582240551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236619398316696013771949605 44366137184380502582240551)
        ·
          refine ⟨66549205776570753873360827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44366137184380502582240551 66549205776570753873360827)
          ·
            refine ⟨99823808664856130810041241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66549205776570753873360827 99823808664856130810041241)
            ·
              refine ⟨74867856498642098107530931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99823808664856130810041241 74867856498642098107530931)
              ·
                refine ⟨112301784747963147161296397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74867856498642098107530931 112301784747963147161296397)
                ·
                  refine ⟨42113169280486180185486149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112301784747963147161296397 42113169280486180185486149)
                  ·
                    refine ⟨7896219240091158784778653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42113169280486180185486149 7896219240091158784778653)
                    ·
                      refine ⟨2961082215034184544291995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7896219240091158784778653 2961082215034184544291995)
                      ·
                        rfl

theorem cell23_5766687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_5766687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766687 prefixEnd_5766687 := by exact prefixLift 5766687
  have htrace : WordTrace (prefixWord ++ tailWord_5766687) baseStart_5766687 baseEnd_5766687 := by
    simpa [prefixWord, tailWord_5766687, baseEnd_5766687] using wordTrace_append hprefix tailTrace_5766687
  have hstable : (prefixWord ++ tailWord_5766687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766687).length < 2 ^ (prefixWord ++ tailWord_5766687).sum := by decide
  have hdescent : baseEnd_5766687 < baseStart_5766687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766737 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 5, 5]
def baseStart_5766737 : Nat := 118140960795 + 5766737 * 2 ^ 59
def prefixEnd_5766737 : Nat := 4983230072969 + 3 ^ 40 * 5766737 * 2
def baseEnd_5766737 : Nat := 987035963022303116222255

theorem tailTrace_5766737 : CollatzResearch.WordTrace tailWord_5766737 prefixEnd_5766737 987035963022303116222255 := by
  unfold tailWord_5766737
  simp only [CollatzResearch.WordTrace]
  refine ⟨210330177709104204114386465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140220118472736136076257643 210330177709104204114386465)
  ·
    refine ⟨157747633281828153085789849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210330177709104204114386465 157747633281828153085789849)
    ·
      refine ⟨118310724961371114814342387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157747633281828153085789849 118310724961371114814342387)
      ·
        refine ⟨177466087442056672221513581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118310724961371114814342387 177466087442056672221513581)
        ·
          refine ⟨66549782790771252083067593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177466087442056672221513581 66549782790771252083067593)
          ·
            refine ⟨49912337093078439062300695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66549782790771252083067593 49912337093078439062300695)
            ·
              refine ⟨74868505639617658593451043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49912337093078439062300695 74868505639617658593451043)
              ·
                refine ⟨112302758459426487890176565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74868505639617658593451043 112302758459426487890176565)
                ·
                  refine ⟨10528383605571233239704053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112302758459426487890176565 10528383605571233239704053)
                  ·
                    refine ⟨987035963022303116222255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10528383605571233239704053 987035963022303116222255)
                    ·
                      rfl

theorem cell23_5766737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_5766737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766737 prefixEnd_5766737 := by exact prefixLift 5766737
  have htrace : WordTrace (prefixWord ++ tailWord_5766737) baseStart_5766737 baseEnd_5766737 := by
    simpa [prefixWord, tailWord_5766737, baseEnd_5766737] using wordTrace_append hprefix tailTrace_5766737
  have hstable : (prefixWord ++ tailWord_5766737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766737).length < 2 ^ (prefixWord ++ tailWord_5766737).sum := by decide
  have hdescent : baseEnd_5766737 < baseStart_5766737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766744 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 1, 5, 2]
def baseStart_5766744 : Nat := 118140960795 + 5766744 * 2 ^ 59
def prefixEnd_5766744 : Nat := 4983230072969 + 3 ^ 40 * 5766744 * 2
def baseEnd_5766744 : Nat := 2961111483431490821279233

theorem tailTrace_5766744 : CollatzResearch.WordTrace tailWord_5766744 prefixEnd_5766744 2961111483431490821279233 := by
  unfold tailWord_5766744
  simp only [CollatzResearch.WordTrace]
  refine ⟨105165216510039422154945643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140220288680052562873260857 105165216510039422154945643)
  ·
    refine ⟨157747824765059133232418465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105165216510039422154945643 157747824765059133232418465)
    ·
      refine ⟨118310868573794349924313849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157747824765059133232418465 118310868573794349924313849)
      ·
        refine ⟨88733151430345762443235387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118310868573794349924313849 88733151430345762443235387)
        ·
          refine ⟨133099727145518643664853081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88733151430345762443235387 133099727145518643664853081)
          ·
            refine ⟨99824795359138982748639811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133099727145518643664853081 99824795359138982748639811)
            ·
              refine ⟨149737193038708474122959717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99824795359138982748639811 149737193038708474122959717)
              ·
                refine ⟨28075723694757838898054947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149737193038708474122959717 28075723694757838898054947)
                ·
                  refine ⟨42113585542136758347082421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28075723694757838898054947 42113585542136758347082421)
                  ·
                    refine ⟨3948148644575321095038977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42113585542136758347082421 3948148644575321095038977)
                    ·
                      refine ⟨2961111483431490821279233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948148644575321095038977 2961111483431490821279233)
                      ·
                        rfl

theorem cell23_5766744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_5766744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766744 prefixEnd_5766744 := by exact prefixLift 5766744
  have htrace : WordTrace (prefixWord ++ tailWord_5766744) baseStart_5766744 baseEnd_5766744 := by
    simpa [prefixWord, tailWord_5766744, baseEnd_5766744] using wordTrace_append hprefix tailTrace_5766744
  have hstable : (prefixWord ++ tailWord_5766744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766744).length < 2 ^ (prefixWord ++ tailWord_5766744).sum := by decide
  have hdescent : baseEnd_5766744 < baseStart_5766744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766761 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 2, 3, 2]
def baseStart_5766761 : Nat := 118140960795 + 5766761 * 2 ^ 59
def prefixEnd_5766761 : Nat := 4983230072969 + 3 ^ 40 * 5766761 * 2
def baseEnd_5766761 : Nat := 2961120212602617254766655

theorem tailTrace_5766761 : CollatzResearch.WordTrace tailWord_5766761 prefixEnd_5766761 2961120212602617254766655 := by
  unfold tailWord_5766761
  simp only [CollatzResearch.WordTrace]
  refine ⟨210331053061017256213260137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140220702040678170808840091 210331053061017256213260137)
  ·
    refine ⟨157748289795762942159945103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210331053061017256213260137 157748289795762942159945103)
    ·
      refine ⟨236622434693644413239917655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157748289795762942159945103 236622434693644413239917655)
      ·
        refine ⟨354933652040466619859876483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236622434693644413239917655 354933652040466619859876483)
        ·
          refine ⟨532400478060699929789814725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354933652040466619859876483 532400478060699929789814725)
          ·
            refine ⟨99825089636381236835590261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 532400478060699929789814725 99825089636381236835590261)
            ·
              refine ⟨9358602153410740953336587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99825089636381236835590261 9358602153410740953336587)
              ·
                refine ⟨14037903230116111430004881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9358602153410740953336587 14037903230116111430004881)
                ·
                  refine ⟨10528427422587083572503661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14037903230116111430004881 10528427422587083572503661)
                  ·
                    refine ⟨3948160283470156339688873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10528427422587083572503661 3948160283470156339688873)
                    ·
                      refine ⟨2961120212602617254766655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948160283470156339688873 2961120212602617254766655)
                      ·
                        rfl

theorem cell23_5766761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 3, 2].length) (baseStart_5766761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766761 prefixEnd_5766761 := by exact prefixLift 5766761
  have htrace : WordTrace (prefixWord ++ tailWord_5766761) baseStart_5766761 baseEnd_5766761 := by
    simpa [prefixWord, tailWord_5766761, baseEnd_5766761] using wordTrace_append hprefix tailTrace_5766761
  have hstable : (prefixWord ++ tailWord_5766761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766761).length < 2 ^ (prefixWord ++ tailWord_5766761).sum := by decide
  have hdescent : baseEnd_5766761 < baseStart_5766761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766768 : List Nat := [2, 1, 1, 1, 6, 1, 1, 5, 1, 1, 3]
def baseStart_5766768 : Nat := 118140960795 + 5766768 * 2 ^ 59
def prefixEnd_5766768 : Nat := 4983230072969 + 3 ^ 40 * 5766768 * 2
def baseEnd_5766768 : Nat := 2961123806967198727379123

theorem tailTrace_5766768 : CollatzResearch.WordTrace tailWord_5766768 prefixEnd_5766768 2961123806967198727379123 := by
  unfold tailWord_5766768
  simp only [CollatzResearch.WordTrace]
  refine ⟨105165654185995948204382479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140220872247994597605843305 105165654185995948204382479)
  ·
    refine ⟨157748481278993922306573719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105165654185995948204382479 157748481278993922306573719)
    ·
      refine ⟨236622721918490883459860579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157748481278993922306573719 236622721918490883459860579)
      ·
        refine ⟨354934082877736325189790869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236622721918490883459860579 354934082877736325189790869)
        ·
          refine ⟨16637535134893890243271447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 354934082877736325189790869 16637535134893890243271447)
          ·
            refine ⟨24956302702340835364907171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16637535134893890243271447 24956302702340835364907171)
            ·
              refine ⟨37434454053511253047360757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24956302702340835364907171 37434454053511253047360757)
              ·
                refine ⟨3509480067516679973190071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37434454053511253047360757 3509480067516679973190071)
                ·
                  refine ⟨5264220101275019959785107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509480067516679973190071 5264220101275019959785107)
                  ·
                    refine ⟨7896330151912529939677661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5264220101275019959785107 7896330151912529939677661)
                    ·
                      refine ⟨2961123806967198727379123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7896330151912529939677661 2961123806967198727379123)
                      ·
                        rfl

theorem cell23_5766768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 1, 3].length) (baseStart_5766768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766768 prefixEnd_5766768 := by exact prefixLift 5766768
  have htrace : WordTrace (prefixWord ++ tailWord_5766768) baseStart_5766768 baseEnd_5766768 := by
    simpa [prefixWord, tailWord_5766768, baseEnd_5766768] using wordTrace_append hprefix tailTrace_5766768
  have hstable : (prefixWord ++ tailWord_5766768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766768).length < 2 ^ (prefixWord ++ tailWord_5766768).sum := by decide
  have hdescent : baseEnd_5766768 < baseStart_5766768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766784 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 4, 4]
def baseStart_5766784 : Nat := 118140960795 + 5766784 * 2 ^ 59
def prefixEnd_5766784 : Nat := 4983230072969 + 3 ^ 40 * 5766784 * 2
def baseEnd_5766784 : Nat := 987044007552556888259683

theorem tailTrace_5766784 : CollatzResearch.WordTrace tailWord_5766784 prefixEnd_5766784 987044007552556888259683 := by
  unfold tailWord_5766784
  simp only [CollatzResearch.WordTrace]
  refine ⟨105165945969966965570673703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140221261293289287427564937 105165945969966965570673703)
  ·
    refine ⟨157748918954950448356010555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105165945969966965570673703 157748918954950448356010555)
    ·
      refine ⟨236623378432425672534015833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157748918954950448356010555 236623378432425672534015833)
      ·
        refine ⟨177467533824319254400511875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236623378432425672534015833 177467533824319254400511875)
        ·
          refine ⟨266201300736478881600767813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177467533824319254400511875 266201300736478881600767813)
          ·
            refine ⟨49912743888089790300143965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266201300736478881600767813 49912743888089790300143965)
            ·
              refine ⟨18717278958033671362553987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49912743888089790300143965 18717278958033671362553987)
              ·
                refine ⟨28075918437050507043830981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18717278958033671362553987 28075918437050507043830981)
                ·
                  refine ⟨5264234706946970070718309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28075918437050507043830981 5264234706946970070718309)
                  ·
                    refine ⟨987044007552556888259683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5264234706946970070718309 987044007552556888259683)
                    ·
                      rfl

theorem cell23_5766784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 4].length) (baseStart_5766784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766784 prefixEnd_5766784 := by exact prefixLift 5766784
  have htrace : WordTrace (prefixWord ++ tailWord_5766784) baseStart_5766784 baseEnd_5766784 := by
    simpa [prefixWord, tailWord_5766784, baseEnd_5766784] using wordTrace_append hprefix tailTrace_5766784
  have hstable : (prefixWord ++ tailWord_5766784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766784).length < 2 ^ (prefixWord ++ tailWord_5766784).sum := by decide
  have hdescent : baseEnd_5766784 < baseStart_5766784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766787 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 6]
def baseStart_5766787 : Nat := 118140960795 + 5766787 * 2 ^ 59
def prefixEnd_5766787 : Nat := 4983230072969 + 3 ^ 40 * 5766787 * 2
def baseEnd_5766787 : Nat := 2961133563099634153041535

theorem tailTrace_5766787 : CollatzResearch.WordTrace tailWord_5766787 prefixEnd_5766787 2961133563099634153041535 := by
  unfold tailWord_5766787
  simp only [CollatzResearch.WordTrace]
  refine ⟨210332001358923062653706615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140221334239282041769137743 210332001358923062653706615)
  ·
    refine ⟨315498002038384593980559923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210332001358923062653706615 315498002038384593980559923)
    ·
      refine ⟨473247003057576890970839885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315498002038384593980559923 473247003057576890970839885)
      ·
        refine ⟨177467626146591334114064957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 473247003057576890970839885 177467626146591334114064957)
        ·
          refine ⟨66550359804971750292774359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177467626146591334114064957 66550359804971750292774359)
          ·
            refine ⟨99825539707457625439161539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66550359804971750292774359 99825539707457625439161539)
            ·
              refine ⟨149738309561186438158742309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99825539707457625439161539 149738309561186438158742309)
              ·
                refine ⟨28075933042722457154764183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149738309561186438158742309 28075933042722457154764183)
                ·
                  refine ⟨42113899564083685732146275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28075933042722457154764183 42113899564083685732146275)
                  ·
                    refine ⟨63170849346125528598219413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42113899564083685732146275 63170849346125528598219413)
                    ·
                      refine ⟨2961133563099634153041535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63170849346125528598219413 2961133563099634153041535)
                      ·
                        rfl

theorem cell23_5766787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_5766787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766787 prefixEnd_5766787 := by exact prefixLift 5766787
  have htrace : WordTrace (prefixWord ++ tailWord_5766787) baseStart_5766787 baseEnd_5766787 := by
    simpa [prefixWord, tailWord_5766787, baseEnd_5766787] using wordTrace_append hprefix tailTrace_5766787
  have hstable : (prefixWord ++ tailWord_5766787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766787).length < 2 ^ (prefixWord ++ tailWord_5766787).sum := by decide
  have hdescent : baseEnd_5766787 < baseStart_5766787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766794 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_5766794 : Nat := 118140960795 + 5766794 * 2 ^ 59
def prefixEnd_5766794 : Nat := 4983230072969 + 3 ^ 40 * 5766794 * 2
def baseEnd_5766794 : Nat := 2961137157464215625654003

theorem tailTrace_5766794 : CollatzResearch.WordTrace tailWord_5766794 prefixEnd_5766794 2961137157464215625654003 := by
  unfold tailWord_5766794
  simp only [CollatzResearch.WordTrace]
  refine ⟨52583064167474425712302859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140221504446598468566140957 52583064167474425712302859)
  ·
    refine ⟨78874596251211638568454289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52583064167474425712302859 78874596251211638568454289)
    ·
      refine ⟨59155947188408728926340717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78874596251211638568454289 59155947188408728926340717)
      ·
        refine ⟨22183480195653273347377769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59155947188408728926340717 22183480195653273347377769)
        ·
          refine ⟨16637610146739955010533327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22183480195653273347377769 16637610146739955010533327)
          ·
            refine ⟨24956415220109932515799991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16637610146739955010533327 24956415220109932515799991)
            ·
              refine ⟨37434622830164898773699987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24956415220109932515799991 37434622830164898773699987)
              ·
                refine ⟨56151934245247348160549981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37434622830164898773699987 56151934245247348160549981)
                ·
                  refine ⟨21056975341967755560206243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56151934245247348160549981 21056975341967755560206243)
                  ·
                    refine ⟨31585463012951633340309365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21056975341967755560206243 31585463012951633340309365)
                    ·
                      refine ⟨2961137157464215625654003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31585463012951633340309365 2961137157464215625654003)
                      ·
                        rfl

theorem cell23_5766794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_5766794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766794 prefixEnd_5766794 := by exact prefixLift 5766794
  have htrace : WordTrace (prefixWord ++ tailWord_5766794) baseStart_5766794 baseEnd_5766794 := by
    simpa [prefixWord, tailWord_5766794, baseEnd_5766794] using wordTrace_append hprefix tailTrace_5766794
  have hstable : (prefixWord ++ tailWord_5766794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766794).length < 2 ^ (prefixWord ++ tailWord_5766794).sum := by decide
  have hdescent : baseEnd_5766794 < baseStart_5766794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766808 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 3, 2, 2]
def baseStart_5766808 : Nat := 118140960795 + 5766808 * 2 ^ 59
def prefixEnd_5766808 : Nat := 4983230072969 + 3 ^ 40 * 5766808 * 2
def baseEnd_5766808 : Nat := 2961144346193378570878939

theorem tailTrace_5766808 : CollatzResearch.WordTrace tailWord_5766808 prefixEnd_5766808 2961144346193378570878939 := by
  unfold tailWord_5766808
  simp only [CollatzResearch.WordTrace]
  refine ⟨105166383645923491620110539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140221844861231322160147385 105166383645923491620110539)
  ·
    refine ⟨157749575468885237430165809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105166383645923491620110539 157749575468885237430165809)
    ·
      refine ⟨118312181601663928072624357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157749575468885237430165809 118312181601663928072624357)
      ·
        refine ⟨22183534050311986513617067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118312181601663928072624357 22183534050311986513617067)
        ·
          refine ⟨33275301075467979770425601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22183534050311986513617067 33275301075467979770425601)
          ·
            refine ⟨24956475806600984827819201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33275301075467979770425601 24956475806600984827819201)
            ·
              refine ⟨18717356854950738620864401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24956475806600984827819201 18717356854950738620864401)
              ·
                refine ⟨14038017641213053965648301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18717356854950738620864401 14038017641213053965648301)
                ·
                  refine ⟨5264256615454895237118113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14038017641213053965648301 5264256615454895237118113)
                  ·
                    refine ⟨3948192461591171427838585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5264256615454895237118113 3948192461591171427838585)
                    ·
                      refine ⟨2961144346193378570878939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948192461591171427838585 2961144346193378570878939)
                      ·
                        rfl

theorem cell23_5766808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_5766808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766808 prefixEnd_5766808 := by exact prefixLift 5766808
  have htrace : WordTrace (prefixWord ++ tailWord_5766808) baseStart_5766808 baseEnd_5766808 := by
    simpa [prefixWord, tailWord_5766808, baseEnd_5766808] using wordTrace_append hprefix tailTrace_5766808
  have hstable : (prefixWord ++ tailWord_5766808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766808).length < 2 ^ (prefixWord ++ tailWord_5766808).sum := by decide
  have hdescent : baseEnd_5766808 < baseStart_5766808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766841 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 3]
def baseStart_5766841 : Nat := 118140960795 + 5766841 * 2 ^ 59
def prefixEnd_5766841 : Nat := 4983230072969 + 3 ^ 40 * 5766841 * 2
def baseEnd_5766841 : Nat := 2961161291054976941766287

theorem tailTrace_5766841 : CollatzResearch.WordTrace tailWord_5766841 prefixEnd_5766841 2961161291054976941766287 := by
  unfold tailWord_5766841
  simp only [CollatzResearch.WordTrace]
  refine ⟨210333970900727429876172377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140222647267151619917448251 210333970900727429876172377)
  ·
    refine ⟨157750478175545572407129283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210333970900727429876172377 157750478175545572407129283)
    ·
      refine ⟨236625717263318358610693925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157750478175545572407129283 236625717263318358610693925)
      ·
        refine ⟨44367321986872192239505111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236625717263318358610693925 44367321986872192239505111)
        ·
          refine ⟨66550982980308288359257667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44367321986872192239505111 66550982980308288359257667)
          ·
            refine ⟨99826474470462432538886501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66550982980308288359257667 99826474470462432538886501)
            ·
              refine ⟨18717463963211706101041219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99826474470462432538886501 18717463963211706101041219)
              ·
                refine ⟨28076195944817559151561829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18717463963211706101041219 28076195944817559151561829)
                ·
                  refine ⟨5264286739653292340917843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28076195944817559151561829 5264286739653292340917843)
                  ·
                    refine ⟨7896430109479938511376765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5264286739653292340917843 7896430109479938511376765)
                    ·
                      refine ⟨2961161291054976941766287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7896430109479938511376765 2961161291054976941766287)
                      ·
                        rfl

theorem cell23_5766841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_5766841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766841 prefixEnd_5766841 := by exact prefixLift 5766841
  have htrace : WordTrace (prefixWord ++ tailWord_5766841) baseStart_5766841 baseEnd_5766841 := by
    simpa [prefixWord, tailWord_5766841, baseEnd_5766841] using wordTrace_append hprefix tailTrace_5766841
  have hstable : (prefixWord ++ tailWord_5766841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766841).length < 2 ^ (prefixWord ++ tailWord_5766841).sum := by decide
  have hdescent : baseEnd_5766841 < baseStart_5766841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766842 : List Nat := [3, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2]
def baseStart_5766842 : Nat := 118140960795 + 5766842 * 2 ^ 59
def prefixEnd_5766842 : Nat := 4983230072969 + 3 ^ 40 * 5766842 * 2
def baseEnd_5766842 : Nat := 2961161804535631437853783

theorem tailTrace_5766842 : CollatzResearch.WordTrace tailWord_5766842 prefixEnd_5766842 2961161804535631437853783 := by
  unfold tailWord_5766842
  simp only [CollatzResearch.WordTrace]
  refine ⟨52583501843430951761739695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140222671582482538031305853 52583501843430951761739695)
  ·
    refine ⟨78875252765146427642609543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52583501843430951761739695 78875252765146427642609543)
    ·
      refine ⟨118312879147719641463914315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78875252765146427642609543 118312879147719641463914315)
      ·
        refine ⟨177469318721579462195871473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118312879147719641463914315 177469318721579462195871473)
        ·
          refine ⟨133101989041184596646903605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177469318721579462195871473 133101989041184596646903605)
          ·
            refine ⟨12478311472611055935647213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133101989041184596646903605 12478311472611055935647213)
            ·
              refine ⟨4679366802229145975867705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12478311472611055935647213 4679366802229145975867705)
              ·
                refine ⟨3509525101671859481900779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4679366802229145975867705 3509525101671859481900779)
                ·
                  refine ⟨5264287652507789222851169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509525101671859481900779 5264287652507789222851169)
                  ·
                    refine ⟨3948215739380841917138377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5264287652507789222851169 3948215739380841917138377)
                    ·
                      refine ⟨2961161804535631437853783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948215739380841917138377 2961161804535631437853783)
                      ·
                        rfl

theorem cell23_5766842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_5766842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766842 prefixEnd_5766842 := by exact prefixLift 5766842
  have htrace : WordTrace (prefixWord ++ tailWord_5766842) baseStart_5766842 baseEnd_5766842 := by
    simpa [prefixWord, tailWord_5766842, baseEnd_5766842] using wordTrace_append hprefix tailTrace_5766842
  have hstable : (prefixWord ++ tailWord_5766842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766842).length < 2 ^ (prefixWord ++ tailWord_5766842).sum := by decide
  have hdescent : baseEnd_5766842 < baseStart_5766842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766884 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_5766884 : Nat := 118140960795 + 5766884 * 2 ^ 59
def prefixEnd_5766884 : Nat := 4983230072969 + 3 ^ 40 * 5766884 * 2
def baseEnd_5766884 : Nat := 2961183370723120273528589

theorem tailTrace_5766884 : CollatzResearch.WordTrace tailWord_5766884 prefixEnd_5766884 2961183370723120273528589 := by
  unfold tailWord_5766884
  simp only [CollatzResearch.WordTrace]
  refine ⟨105167769619785824109993853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140223692826381098813325137 105167769619785824109993853)
  ·
    refine ⟨39437913607419684041247695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105167769619785824109993853 39437913607419684041247695)
    ·
      refine ⟨59156870411129526061871543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39437913607419684041247695 59156870411129526061871543)
      ·
        refine ⟨88735305616694289092807315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59156870411129526061871543 88735305616694289092807315)
        ·
          refine ⟨133102958425041433639210973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88735305616694289092807315 133102958425041433639210973)
          ·
            refine ⟨49913609409390537614704115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133102958425041433639210973 49913609409390537614704115)
            ·
              refine ⟨74870414114085806422056173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49913609409390537614704115 74870414114085806422056173)
              ·
                refine ⟨28076405292782177408271065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74870414114085806422056173 28076405292782177408271065)
                ·
                  refine ⟨21057303969586633056203299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28076405292782177408271065 21057303969586633056203299)
                  ·
                    refine ⟨31585955954379949584304949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21057303969586633056203299 31585955954379949584304949)
                    ·
                      refine ⟨2961183370723120273528589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31585955954379949584304949 2961183370723120273528589)
                      ·
                        rfl

theorem cell23_5766884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_5766884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766884 prefixEnd_5766884 := by exact prefixLift 5766884
  have htrace : WordTrace (prefixWord ++ tailWord_5766884) baseStart_5766884 baseEnd_5766884 := by
    simpa [prefixWord, tailWord_5766884, baseEnd_5766884] using wordTrace_append hprefix tailTrace_5766884
  have hstable : (prefixWord ++ tailWord_5766884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766884).length < 2 ^ (prefixWord ++ tailWord_5766884).sum := by decide
  have hdescent : baseEnd_5766884 < baseStart_5766884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766885 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 1, 3, 2]
def baseStart_5766885 : Nat := 118140960795 + 5766885 * 2 ^ 59
def prefixEnd_5766885 : Nat := 4983230072969 + 3 ^ 40 * 5766885 * 2
def baseEnd_5766885 : Nat := 2961183884203774769616085

theorem tailTrace_5766885 : CollatzResearch.WordTrace tailWord_5766885 prefixEnd_5766885 2961183884203774769616085 := by
  unfold tailWord_5766885
  simp only [CollatzResearch.WordTrace]
  refine ⟨210335575712568025390774109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140223717141712016927182739 210335575712568025390774109)
  ·
    refine ⟨78875840892213009521540291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210335575712568025390774109 78875840892213009521540291)
    ·
      refine ⟨118313761338319514282310437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78875840892213009521540291 118313761338319514282310437)
      ·
        refine ⟨22183830250934908927933207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118313761338319514282310437 22183830250934908927933207)
        ·
          refine ⟨33275745376402363391899811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22183830250934908927933207 33275745376402363391899811)
          ·
            refine ⟨49913618064603545087849717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33275745376402363391899811 49913618064603545087849717)
            ·
              refine ⟨4679401693556582351985911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49913618064603545087849717 4679401693556582351985911)
              ·
                refine ⟨7019102540334873527978867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4679401693556582351985911 7019102540334873527978867)
                ·
                  refine ⟨10528653810502310291968301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7019102540334873527978867 10528653810502310291968301)
                  ·
                    refine ⟨3948245178938366359488113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10528653810502310291968301 3948245178938366359488113)
                    ·
                      refine ⟨2961183884203774769616085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948245178938366359488113 2961183884203774769616085)
                      ·
                        rfl

theorem cell23_5766885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_5766885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766885 prefixEnd_5766885 := by exact prefixLift 5766885
  have htrace : WordTrace (prefixWord ++ tailWord_5766885) baseStart_5766885 baseEnd_5766885 := by
    simpa [prefixWord, tailWord_5766885, baseEnd_5766885] using wordTrace_append hprefix tailTrace_5766885
  have hstable : (prefixWord ++ tailWord_5766885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766885).length < 2 ^ (prefixWord ++ tailWord_5766885).sum := by decide
  have hdescent : baseEnd_5766885 < baseStart_5766885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766938 : List Nat := [3, 1, 1, 3, 2, 3, 2, 3, 5]
def baseStart_5766938 : Nat := 118140960795 + 5766938 * 2 ^ 59
def prefixEnd_5766938 : Nat := 4983230072969 + 3 ^ 40 * 5766938 * 2
def baseEnd_5766938 : Nat := 329023455408718118028149

theorem tailTrace_5766938 : CollatzResearch.WordTrace tailWord_5766938 prefixEnd_5766938 329023455408718118028149 := by
  unfold tailWord_5766938
  simp only [CollatzResearch.WordTrace]
  refine ⟨52584377195344003860613367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140225005854250676961635645 52584377195344003860613367)
  ·
    refine ⟨78876565793016005790920051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52584377195344003860613367 78876565793016005790920051)
    ·
      refine ⟨118314848689524008686380077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78876565793016005790920051 118314848689524008686380077)
      ·
        refine ⟨44368068258571503257392529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118314848689524008686380077 44368068258571503257392529)
        ·
          refine ⟨33276051193928627443044397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44368068258571503257392529 33276051193928627443044397)
          ·
            refine ⟨12478519197723235291141649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33276051193928627443044397 12478519197723235291141649)
            ·
              refine ⟨9358889398292426468356237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12478519197723235291141649 9358889398292426468356237)
              ·
                refine ⟨3509583524359659925633589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9358889398292426468356237 3509583524359659925633589)
                ·
                  refine ⟨329023455408718118028149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3509583524359659925633589 329023455408718118028149)
                  ·
                    rfl

theorem cell23_5766938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_5766938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766938 prefixEnd_5766938 := by exact prefixLift 5766938
  have htrace : WordTrace (prefixWord ++ tailWord_5766938) baseStart_5766938 baseEnd_5766938 := by
    simpa [prefixWord, tailWord_5766938, baseEnd_5766938] using wordTrace_append hprefix tailTrace_5766938
  have hstable : (prefixWord ++ tailWord_5766938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766938).length < 2 ^ (prefixWord ++ tailWord_5766938).sum := by decide
  have hdescent : baseEnd_5766938 < baseStart_5766938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5766981 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_5766981 : Nat := 118140960795 + 5766981 * 2 ^ 59
def prefixEnd_5766981 : Nat := 4983230072969 + 3 ^ 40 * 5766981 * 2
def baseEnd_5766981 : Nat := 987077726115535464671881

theorem tailTrace_5766981 : CollatzResearch.WordTrace tailWord_5766981 prefixEnd_5766981 987077726115535464671881 := by
  unfold tailWord_5766981
  simp only [CollatzResearch.WordTrace]
  refine ⟨210339077120220233786268797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140226051413480155857512531 210339077120220233786268797)
  ·
    refine ⟨78877153920082587669850799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210339077120220233786268797 78877153920082587669850799)
    ·
      refine ⟨118315730880123881504776199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78877153920082587669850799 118315730880123881504776199)
      ·
        refine ⟨177473596320185822257164299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118315730880123881504776199 177473596320185822257164299)
        ·
          refine ⟨266210394480278733385746449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177473596320185822257164299 266210394480278733385746449)
          ·
            refine ⟨199657795860209050039309837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266210394480278733385746449 199657795860209050039309837)
            ·
              refine ⟨74871673447578393764741189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199657795860209050039309837 74871673447578393764741189)
              ·
                refine ⟨14038438771420948830888973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74871673447578393764741189 14038438771420948830888973)
                ·
                  refine ⟨5264414539282855811583365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14038438771420948830888973 5264414539282855811583365)
                  ·
                    refine ⟨987077726115535464671881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5264414539282855811583365 987077726115535464671881)
                    ·
                      rfl

theorem cell23_5766981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_5766981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5766981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5766981 prefixEnd_5766981 := by exact prefixLift 5766981
  have htrace : WordTrace (prefixWord ++ tailWord_5766981) baseStart_5766981 baseEnd_5766981 := by
    simpa [prefixWord, tailWord_5766981, baseEnd_5766981] using wordTrace_append hprefix tailTrace_5766981
  have hstable : (prefixWord ++ tailWord_5766981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5766981).length < 2 ^ (prefixWord ++ tailWord_5766981).sum := by decide
  have hdescent : baseEnd_5766981 < baseStart_5766981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5766981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767008 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 3]
def baseStart_5767008 : Nat := 118140960795 + 5767008 * 2 ^ 59
def prefixEnd_5767008 : Nat := 4983230072969 + 3 ^ 40 * 5767008 * 2
def baseEnd_5767008 : Nat := 2961247042324277788378019

theorem tailTrace_5767008 : CollatzResearch.WordTrace tailWord_5767008 prefixEnd_5767008 2961247042324277788378019 := by
  unfold tailWord_5767008
  simp only [CollatzResearch.WordTrace]
  refine ⟨105170030945561208698750839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140226707927414944931667785 105170030945561208698750839)
  ·
    refine ⟨157755046418341813048126259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105170030945561208698750839 157755046418341813048126259)
    ·
      refine ⟨236632569627512719572189389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157755046418341813048126259 236632569627512719572189389)
      ·
        refine ⟨88737213610317269839571021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236632569627512719572189389 88737213610317269839571021)
        ·
          refine ⟨33276455103868976189839133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88737213610317269839571021 33276455103868976189839133)
          ·
            refine ⟨12478670663950866071189675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33276455103868976189839133 12478670663950866071189675)
            ·
              refine ⟨18718005995926299106784513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12478670663950866071189675 18718005995926299106784513)
              ·
                refine ⟨14038504496944724330088385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18718005995926299106784513 14038504496944724330088385)
                ·
                  refine ⟨10528878372708543247566289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14038504496944724330088385 10528878372708543247566289)
                  ·
                    refine ⟨7896658779531407435674717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10528878372708543247566289 7896658779531407435674717)
                    ·
                      refine ⟨2961247042324277788378019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7896658779531407435674717 2961247042324277788378019)
                      ·
                        rfl

theorem cell23_5767008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_5767008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767008 prefixEnd_5767008 := by exact prefixLift 5767008
  have htrace : WordTrace (prefixWord ++ tailWord_5767008) baseStart_5767008 baseEnd_5767008 := by
    simpa [prefixWord, tailWord_5767008, baseEnd_5767008] using wordTrace_append hprefix tailTrace_5767008
  have hstable : (prefixWord ++ tailWord_5767008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767008).length < 2 ^ (prefixWord ++ tailWord_5767008).sum := by decide
  have hdescent : baseEnd_5767008 < baseStart_5767008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767024 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 2, 9]
def baseStart_5767024 : Nat := 118140960795 + 5767024 * 2 ^ 59
def prefixEnd_5767024 : Nat := 4983230072969 + 3 ^ 40 * 5767024 * 2
def baseEnd_5767024 : Nat := 987085086004916575259315

theorem tailTrace_5767024 : CollatzResearch.WordTrace tailWord_5767024 prefixEnd_5767024 987085086004916575259315 := by
  unfold tailWord_5767024
  simp only [CollatzResearch.WordTrace]
  refine ⟨105170322729532226065042063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140227096972709634753389417 105170322729532226065042063)
  ·
    refine ⟨157755484094298339097563095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105170322729532226065042063 157755484094298339097563095)
    ·
      refine ⟨236633226141447508646344643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157755484094298339097563095 236633226141447508646344643)
      ·
        refine ⟨354949839212171262969516965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236633226141447508646344643 354949839212171262969516965)
        ·
          refine ⟨66553094852282111806784431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354949839212171262969516965 66553094852282111806784431)
          ·
            refine ⟨99829642278423167710176647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66553094852282111806784431 99829642278423167710176647)
            ·
              refine ⟨149744463417634751565264971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99829642278423167710176647 149744463417634751565264971)
              ·
                refine ⟨224616695126452127347897457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149744463417634751565264971 224616695126452127347897457)
                ·
                  refine ⟨168462521344839095510923093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224616695126452127347897457 168462521344839095510923093)
                  ·
                    refine ⟨987085086004916575259315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 168462521344839095510923093 987085086004916575259315)
                    ·
                      rfl

theorem cell23_5767024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_5767024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767024 prefixEnd_5767024 := by exact prefixLift 5767024
  have htrace : WordTrace (prefixWord ++ tailWord_5767024) baseStart_5767024 baseEnd_5767024 := by
    simpa [prefixWord, tailWord_5767024, baseEnd_5767024] using wordTrace_append hprefix tailTrace_5767024
  have hstable : (prefixWord ++ tailWord_5767024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767024).length < 2 ^ (prefixWord ++ tailWord_5767024).sum := by decide
  have hdescent : baseEnd_5767024 < baseStart_5767024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767112 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_5767112 : Nat := 118140960795 + 5767112 * 2 ^ 59
def prefixEnd_5767112 : Nat := 4983230072969 + 3 ^ 40 * 5767112 * 2
def baseEnd_5767112 : Nat := 2961300444312345381477541

theorem tailTrace_5767112 : CollatzResearch.WordTrace tailWord_5767112 prefixEnd_5767112 2961300444312345381477541 := by
  unfold tailWord_5767112
  simp only [CollatzResearch.WordTrace]
  refine ⟨105171927541372821579643795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140229236721830428772858393 105171927541372821579643795)
  ·
    refine ⟨157757891312059232369465693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105171927541372821579643795 157757891312059232369465693)
    ·
      refine ⟨59159209242022212138549635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157757891312059232369465693 59159209242022212138549635)
      ·
        refine ⟨88738813863033318207824453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59159209242022212138549635 88738813863033318207824453)
        ·
          refine ⟨16638527599318747163967085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88738813863033318207824453 16638527599318747163967085)
          ·
            refine ⟨6239447849744530186487657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16638527599318747163967085 6239447849744530186487657)
            ·
              refine ⟨4679585887308397639865743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6239447849744530186487657 4679585887308397639865743)
              ·
                refine ⟨7019378830962596459798615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4679585887308397639865743 7019378830962596459798615)
                ·
                  refine ⟨10529068246443894689697923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7019378830962596459798615 10529068246443894689697923)
                  ·
                    refine ⟨15793602369665842034546885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10529068246443894689697923 15793602369665842034546885)
                    ·
                      refine ⟨2961300444312345381477541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15793602369665842034546885 2961300444312345381477541)
                      ·
                        rfl

theorem cell23_5767112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_5767112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767112 prefixEnd_5767112 := by exact prefixLift 5767112
  have htrace : WordTrace (prefixWord ++ tailWord_5767112) baseStart_5767112 baseEnd_5767112 := by
    simpa [prefixWord, tailWord_5767112, baseEnd_5767112] using wordTrace_append hprefix tailTrace_5767112
  have hstable : (prefixWord ++ tailWord_5767112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767112).length < 2 ^ (prefixWord ++ tailWord_5767112).sum := by decide
  have hdescent : baseEnd_5767112 < baseStart_5767112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767149 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5767149 : Nat := 118140960795 + 5767149 * 2 ^ 59
def prefixEnd_5767149 : Nat := 4983230072969 + 3 ^ 40 * 5767149 * 2
def baseEnd_5767149 : Nat := 2961319443096561736714871

theorem tailTrace_5767149 : CollatzResearch.WordTrace tailWord_5767149 prefixEnd_5767149 2961319443096561736714871 := by
  unfold tailWord_5767149
  simp only [CollatzResearch.WordTrace]
  refine ⟨210345204583611598478384501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140230136389074398985589667 210345204583611598478384501)
  ·
    refine ⟨19719862929713587357348547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210345204583611598478384501 19719862929713587357348547)
    ·
      refine ⟨29579794394570381036022821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19719862929713587357348547 29579794394570381036022821)
      ·
        refine ⟨5546211448981946444254279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29579794394570381036022821 5546211448981946444254279)
        ·
          refine ⟨8319317173472919666381419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5546211448981946444254279 8319317173472919666381419)
          ·
            refine ⟨12478975760209379499572129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8319317173472919666381419 12478975760209379499572129)
            ·
              refine ⟨9359231820157034624679097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12478975760209379499572129 9359231820157034624679097)
              ·
                refine ⟨7019423865117775968509323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9359231820157034624679097 7019423865117775968509323)
                ·
                  refine ⟨10529135797676663952763985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7019423865117775968509323 10529135797676663952763985)
                  ·
                    refine ⟨7896851848257497964572989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10529135797676663952763985 7896851848257497964572989)
                    ·
                      refine ⟨2961319443096561736714871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7896851848257497964572989 2961319443096561736714871)
                      ·
                        rfl

theorem cell23_5767149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5767149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767149 prefixEnd_5767149 := by exact prefixLift 5767149
  have htrace : WordTrace (prefixWord ++ tailWord_5767149) baseStart_5767149 baseEnd_5767149 := by
    simpa [prefixWord, tailWord_5767149, baseEnd_5767149] using wordTrace_append hprefix tailTrace_5767149
  have hstable : (prefixWord ++ tailWord_5767149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767149).length < 2 ^ (prefixWord ++ tailWord_5767149).sum := by decide
  have hdescent : baseEnd_5767149 < baseStart_5767149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767258 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_5767258 : Nat := 118140960795 + 5767258 * 2 ^ 59
def prefixEnd_5767258 : Nat := 4983230072969 + 3 ^ 40 * 5767258 * 2
def baseEnd_5767258 : Nat := 2961375412487901810251869

theorem tailTrace_5767258 : CollatzResearch.WordTrace tailWord_5767258 prefixEnd_5767258 2961375412487901810251869 := by
  unfold tailWord_5767258
  simp only [CollatzResearch.WordTrace]
  refine ⟨52587295035054177523525607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140232786760144473396068285 52587295035054177523525607)
  ·
    refine ⟨78880942552581266285288411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52587295035054177523525607 78880942552581266285288411)
    ·
      refine ⟨118321413828871899427932617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78880942552581266285288411 118321413828871899427932617)
      ·
        refine ⟨88741060371653924570949463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118321413828871899427932617 88741060371653924570949463)
        ·
          refine ⟨133111590557480886856424195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88741060371653924570949463 133111590557480886856424195)
          ·
            refine ⟨199667385836221330284636293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133111590557480886856424195 199667385836221330284636293)
            ·
              refine ⟨37437634844291499428369305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199667385836221330284636293 37437634844291499428369305)
              ·
                refine ⟨28078226133218624571276979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37437634844291499428369305 28078226133218624571276979)
                ·
                  refine ⟨42117339199827936856915469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28078226133218624571276979 42117339199827936856915469)
                  ·
                    refine ⟨15794002199935476321343301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42117339199827936856915469 15794002199935476321343301)
                    ·
                      refine ⟨2961375412487901810251869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15794002199935476321343301 2961375412487901810251869)
                      ·
                        rfl

theorem cell23_5767258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_5767258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767258 prefixEnd_5767258 := by exact prefixLift 5767258
  have htrace : WordTrace (prefixWord ++ tailWord_5767258) baseStart_5767258 baseEnd_5767258 := by
    simpa [prefixWord, tailWord_5767258, baseEnd_5767258] using wordTrace_append hprefix tailTrace_5767258
  have hstable : (prefixWord ++ tailWord_5767258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767258).length < 2 ^ (prefixWord ++ tailWord_5767258).sum := by decide
  have hdescent : baseEnd_5767258 < baseStart_5767258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767352 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 2, 3, 2]
def baseStart_5767352 : Nat := 118140960795 + 5767352 * 2 ^ 59
def prefixEnd_5767352 : Nat := 4983230072969 + 3 ^ 40 * 5767352 * 2
def baseEnd_5767352 : Nat := 2961423679669424442476437

theorem tailTrace_5767352 : CollatzResearch.WordTrace tailWord_5767352 prefixEnd_5767352 2961423679669424442476437 := by
  unfold tailWord_5767352
  simp only [CollatzResearch.WordTrace]
  refine ⟨105176304300938082074012155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140235072401250776098682873 105176304300938082074012155)
  ·
    refine ⟨157764456451407123111018233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105176304300938082074012155 157764456451407123111018233)
    ·
      refine ⟨118323342338555342333263675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157764456451407123111018233 118323342338555342333263675)
      ·
        refine ⟨177485013507833013499895513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118323342338555342333263675 177485013507833013499895513)
        ·
          refine ⟨133113760130874760124921635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177485013507833013499895513 133113760130874760124921635)
          ·
            refine ⟨199670640196312140187382453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133113760130874760124921635 199670640196312140187382453)
            ·
              refine ⟨18719122518404263142567105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199670640196312140187382453 18719122518404263142567105)
              ·
                refine ⟨14039341888803197356925329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18719122518404263142567105 14039341888803197356925329)
                ·
                  refine ⟨10529506416602398017693997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14039341888803197356925329 10529506416602398017693997)
                  ·
                    refine ⟨3948564906225899256635249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10529506416602398017693997 3948564906225899256635249)
                    ·
                      refine ⟨2961423679669424442476437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948564906225899256635249 2961423679669424442476437)
                      ·
                        rfl

theorem cell23_5767352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_5767352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767352 prefixEnd_5767352 := by exact prefixLift 5767352
  have htrace : WordTrace (prefixWord ++ tailWord_5767352) baseStart_5767352 baseEnd_5767352 := by
    simpa [prefixWord, tailWord_5767352, baseEnd_5767352] using wordTrace_append hprefix tailTrace_5767352
  have hstable : (prefixWord ++ tailWord_5767352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767352).length < 2 ^ (prefixWord ++ tailWord_5767352).sum := by decide
  have hdescent : baseEnd_5767352 < baseStart_5767352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767405 : List Nat := [1, 5, 1, 2, 3, 11]
def baseStart_5767405 : Nat := 118140960795 + 5767405 * 2 ^ 59
def prefixEnd_5767405 : Nat := 4983230072969 + 3 ^ 40 * 5767405 * 2
def baseEnd_5767405 : Nat := 12187040716642439239151

theorem tailTrace_5767405 : CollatzResearch.WordTrace tailWord_5767405 prefixEnd_5767405 12187040716642439239151 := by
  unfold tailWord_5767405
  simp only [CollatzResearch.WordTrace]
  refine ⟨210354541670684154199703669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140236361113789436133135779 210354541670684154199703669)
  ·
    refine ⟨19720738281626639456222219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210354541670684154199703669 19720738281626639456222219)
    ·
      refine ⟨29581107422439959184333329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19720738281626639456222219 29581107422439959184333329)
      ·
        refine ⟨22185830566829969388249997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29581107422439959184333329 22185830566829969388249997)
        ·
          refine ⟨8319686462561238520593749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22185830566829969388249997 8319686462561238520593749)
          ·
            refine ⟨12187040716642439239151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8319686462561238520593749 12187040716642439239151)
            ·
              rfl

theorem cell23_5767405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 11].length) (baseStart_5767405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767405 prefixEnd_5767405 := by exact prefixLift 5767405
  have htrace : WordTrace (prefixWord ++ tailWord_5767405) baseStart_5767405 baseEnd_5767405 := by
    simpa [prefixWord, tailWord_5767405, baseEnd_5767405] using wordTrace_append hprefix tailTrace_5767405
  have hstable : (prefixWord ++ tailWord_5767405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767405).length < 2 ^ (prefixWord ++ tailWord_5767405).sum := by decide
  have hdescent : baseEnd_5767405 < baseStart_5767405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767432 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_5767432 : Nat := 118140960795 + 5767432 * 2 ^ 59
def prefixEnd_5767432 : Nat := 4983230072969 + 3 ^ 40 * 5767432 * 2
def baseEnd_5767432 : Nat := 2961464758121784129476069

theorem tailTrace_5767432 : CollatzResearch.WordTrace tailWord_5767432 prefixEnd_5767432 2961464758121784129476069 := by
  unfold tailWord_5767432
  simp only [CollatzResearch.WordTrace]
  refine ⟨105177763220793168905468275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140237017627724225207291033 105177763220793168905468275)
  ·
    refine ⟨157766644831189753358202413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105177763220793168905468275 157766644831189753358202413)
    ·
      refine ⟨59162491811696157509325905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157766644831189753358202413 59162491811696157509325905)
      ·
        refine ⟨44371868858772118131994429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59162491811696157509325905 44371868858772118131994429)
        ·
          refine ⟨16639450822039544299497911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44371868858772118131994429 16639450822039544299497911)
          ·
            refine ⟨24959176233059316449246867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16639450822039544299497911 24959176233059316449246867)
            ·
              refine ⟨37438764349588974673870301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24959176233059316449246867 37438764349588974673870301)
              ·
                refine ⟨14039536631095865502701363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37438764349588974673870301 14039536631095865502701363)
                ·
                  refine ⟨21059304946643798254052045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14039536631095865502701363 21059304946643798254052045)
                  ·
                    refine ⟨7897239354991424345269517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21059304946643798254052045 7897239354991424345269517)
                    ·
                      refine ⟨2961464758121784129476069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7897239354991424345269517 2961464758121784129476069)
                      ·
                        rfl

theorem cell23_5767432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_5767432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767432 prefixEnd_5767432 := by exact prefixLift 5767432
  have htrace : WordTrace (prefixWord ++ tailWord_5767432) baseStart_5767432 baseEnd_5767432 := by
    simpa [prefixWord, tailWord_5767432, baseEnd_5767432] using wordTrace_append hprefix tailTrace_5767432
  have hstable : (prefixWord ++ tailWord_5767432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767432).length < 2 ^ (prefixWord ++ tailWord_5767432).sum := by decide
  have hdescent : baseEnd_5767432 < baseStart_5767432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767453 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_5767453 : Nat := 118140960795 + 5767453 * 2 ^ 59
def prefixEnd_5767453 : Nat := 4983230072969 + 3 ^ 40 * 5767453 * 2
def baseEnd_5767453 : Nat := 2961475541215528547313473

theorem tailTrace_5767453 : CollatzResearch.WordTrace tailWord_5767453 prefixEnd_5767453 2961475541215528547313473 := by
  unfold tailWord_5767453
  simp only [CollatzResearch.WordTrace]
  refine ⟨210356292374510258397451013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140237528249673505598300675 210356292374510258397451013)
  ·
    refine ⟨39441804820220673449522065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210356292374510258397451013 39441804820220673449522065)
    ·
      refine ⟨29581353615165505087141549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39441804820220673449522065 29581353615165505087141549)
      ·
        refine ⟨11093007605687064407678081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29581353615165505087141549 11093007605687064407678081)
        ·
          refine ⟨8319755704265298305758561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11093007605687064407678081 8319755704265298305758561)
          ·
            refine ⟨6239816778198973729318921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8319755704265298305758561 6239816778198973729318921)
            ·
              refine ⟨4679862583649230296989191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6239816778198973729318921 4679862583649230296989191)
              ·
                refine ⟨7019793875473845445483787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4679862583649230296989191 7019793875473845445483787)
                ·
                  refine ⟨10529690813210768168225681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7019793875473845445483787 10529690813210768168225681)
                  ·
                    refine ⟨7897268109908076126169261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10529690813210768168225681 7897268109908076126169261)
                    ·
                      refine ⟨2961475541215528547313473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7897268109908076126169261 2961475541215528547313473)
                      ·
                        rfl

theorem cell23_5767453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_5767453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767453 prefixEnd_5767453 := by exact prefixLift 5767453
  have htrace : WordTrace (prefixWord ++ tailWord_5767453) baseStart_5767453 baseEnd_5767453 := by
    simpa [prefixWord, tailWord_5767453, baseEnd_5767453] using wordTrace_append hprefix tailTrace_5767453
  have hstable : (prefixWord ++ tailWord_5767453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767453).length < 2 ^ (prefixWord ++ tailWord_5767453).sum := by decide
  have hdescent : baseEnd_5767453 < baseStart_5767453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767459 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 1, 3, 2]
def baseStart_5767459 : Nat := 118140960795 + 5767459 * 2 ^ 59
def prefixEnd_5767459 : Nat := 4983230072969 + 3 ^ 40 * 5767459 * 2
def baseEnd_5767459 : Nat := 2961478622099455523838445

theorem tailTrace_5767459 : CollatzResearch.WordTrace tailWord_5767459 prefixEnd_5767459 2961478622099455523838445 := by
  unfold tailWord_5767459
  simp only [CollatzResearch.WordTrace]
  refine ⟨210356511212488521422169431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140237674141659014281446287 210356511212488521422169431)
  ·
    refine ⟨315534766818732782133254147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210356511212488521422169431 315534766818732782133254147)
    ·
      refine ⟨473302150228099173199881221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315534766818732782133254147 473302150228099173199881221)
      ·
        refine ⟨88744153167768594974977729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 473302150228099173199881221 88744153167768594974977729)
        ·
          refine ⟨66558114875826446231233297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88744153167768594974977729 66558114875826446231233297)
          ·
            refine ⟨49918586156869834673424973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66558114875826446231233297 49918586156869834673424973)
            ·
              refine ⟨18719469808826188002534365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49918586156869834673424973 18719469808826188002534365)
              ·
                refine ⟨7019801178309820500950387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18719469808826188002534365 7019801178309820500950387)
                ·
                  refine ⟨10529701767464730751425581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7019801178309820500950387 10529701767464730751425581)
                  ·
                    refine ⟨3948638162799274031784593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10529701767464730751425581 3948638162799274031784593)
                    ·
                      refine ⟨2961478622099455523838445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948638162799274031784593 2961478622099455523838445)
                      ·
                        rfl

theorem cell23_5767459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_5767459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767459 prefixEnd_5767459 := by exact prefixLift 5767459
  have htrace : WordTrace (prefixWord ++ tailWord_5767459) baseStart_5767459 baseEnd_5767459 := by
    simpa [prefixWord, tailWord_5767459, baseEnd_5767459] using wordTrace_append hprefix tailTrace_5767459
  have hstable : (prefixWord ++ tailWord_5767459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767459).length < 2 ^ (prefixWord ++ tailWord_5767459).sum := by decide
  have hdescent : baseEnd_5767459 < baseStart_5767459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767466 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5767466 : Nat := 118140960795 + 5767466 * 2 ^ 59
def prefixEnd_5767466 : Nat := 4983230072969 + 3 ^ 40 * 5767466 * 2
def baseEnd_5767466 : Nat := 2961482216464036996450913

theorem tailTrace_5767466 : CollatzResearch.WordTrace tailWord_5767466 prefixEnd_5767466 2961482216464036996450913 := by
  unfold tailWord_5767466
  simp only [CollatzResearch.WordTrace]
  refine ⟨52589191630865790404418563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140237844348975441078449501 52589191630865790404418563)
  ·
    refine ⟨78883787446298685606627845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52589191630865790404418563 78883787446298685606627845)
    ·
      refine ⟨14790710146181003551242721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78883787446298685606627845 14790710146181003551242721)
      ·
        refine ⟨11093032609635752663432041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14790710146181003551242721 11093032609635752663432041)
        ·
          refine ⟨8319774457226814497574031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11093032609635752663432041 8319774457226814497574031)
          ·
            refine ⟨12479661685840221746361047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8319774457226814497574031 12479661685840221746361047)
            ·
              refine ⟨18719492528760332619541571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12479661685840221746361047 18719492528760332619541571)
              ·
                refine ⟨28079238793140498929312357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18719492528760332619541571 28079238793140498929312357)
                ·
                  refine ⟨5264857273713843549246067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28079238793140498929312357 5264857273713843549246067)
                  ·
                    refine ⟨7897285910570765323869101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5264857273713843549246067 7897285910570765323869101)
                    ·
                      refine ⟨2961482216464036996450913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7897285910570765323869101 2961482216464036996450913)
                      ·
                        rfl

theorem cell23_5767466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5767466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767466 prefixEnd_5767466 := by exact prefixLift 5767466
  have htrace : WordTrace (prefixWord ++ tailWord_5767466) baseStart_5767466 baseEnd_5767466 := by
    simpa [prefixWord, tailWord_5767466, baseEnd_5767466] using wordTrace_append hprefix tailTrace_5767466
  have hstable : (prefixWord ++ tailWord_5767466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767466).length < 2 ^ (prefixWord ++ tailWord_5767466).sum := by decide
  have hdescent : baseEnd_5767466 < baseStart_5767466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767495 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 7]
def baseStart_5767495 : Nat := 118140960795 + 5767495 * 2 ^ 59
def prefixEnd_5767495 : Nat := 4983230072969 + 3 ^ 40 * 5767495 * 2
def baseEnd_5767495 : Nat := 329055234155890820332031

theorem tailTrace_5767495 : CollatzResearch.WordTrace tailWord_5767495 prefixEnd_5767495 329055234155890820332031 := by
  unfold tailWord_5767495
  simp only [CollatzResearch.WordTrace]
  refine ⟨210357824240358099570479939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140238549493572066380319959 210357824240358099570479939)
  ·
    refine ⟨315536736360537149355719909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210357824240358099570479939 315536736360537149355719909)
    ·
      refine ⟨59163138067600715504197483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315536736360537149355719909 59163138067600715504197483)
      ·
        refine ⟨88744707101401073256296225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59163138067600715504197483 88744707101401073256296225)
        ·
          refine ⟨66558530326050804942222169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88744707101401073256296225 66558530326050804942222169)
          ·
            refine ⟨49918897744538103706666627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66558530326050804942222169 49918897744538103706666627)
            ·
              refine ⟨74878346616807155559999941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49918897744538103706666627 74878346616807155559999941)
              ·
                refine ⟨14039689990651341667499989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74878346616807155559999941 14039689990651341667499989)
                ·
                  refine ⟨329055234155890820332031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14039689990651341667499989 329055234155890820332031)
                  ·
                    rfl

theorem cell23_5767495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 7].length) (baseStart_5767495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767495 prefixEnd_5767495 := by exact prefixLift 5767495
  have htrace : WordTrace (prefixWord ++ tailWord_5767495) baseStart_5767495 baseEnd_5767495 := by
    simpa [prefixWord, tailWord_5767495, baseEnd_5767495] using wordTrace_append hprefix tailTrace_5767495
  have hstable : (prefixWord ++ tailWord_5767495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767495).length < 2 ^ (prefixWord ++ tailWord_5767495).sum := by decide
  have hdescent : baseEnd_5767495 < baseStart_5767495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767512 : List Nat := [2, 1, 2, 2, 1, 1, 2, 7, 5]
def baseStart_5767512 : Nat := 118140960795 + 5767512 * 2 ^ 59
def prefixEnd_5767512 : Nat := 4983230072969 + 3 ^ 40 * 5767512 * 2
def baseEnd_5767512 : Nat := 329056204063793757386189

theorem tailTrace_5767512 : CollatzResearch.WordTrace tailWord_5767512 prefixEnd_5767512 329056204063793757386189 := by
  unfold tailWord_5767512
  simp only [CollatzResearch.WordTrace]
  refine ⟨105179222140648255736924395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140238962854197674315899193 105179222140648255736924395)
  ·
    refine ⟨157768833210972383605386593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105179222140648255736924395 157768833210972383605386593)
    ·
      refine ⟨118326624908229287704039945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157768833210972383605386593 118326624908229287704039945)
      ·
        refine ⟨88744968681171965778029959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118326624908229287704039945 88744968681171965778029959)
        ·
          refine ⟨133117453021757948667044939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88744968681171965778029959 133117453021757948667044939)
          ·
            refine ⟨199676179532636923000567409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133117453021757948667044939 199676179532636923000567409)
            ·
              refine ⟨149757134649477692250425557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199676179532636923000567409 149757134649477692250425557)
              ·
                refine ⟨3509932843347133412119349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149757134649477692250425557 3509932843347133412119349)
                ·
                  refine ⟨329056204063793757386189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3509932843347133412119349 329056204063793757386189)
                  ·
                    rfl

theorem cell23_5767512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 5].length) (baseStart_5767512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767512 prefixEnd_5767512 := by exact prefixLift 5767512
  have htrace : WordTrace (prefixWord ++ tailWord_5767512) baseStart_5767512 baseEnd_5767512 := by
    simpa [prefixWord, tailWord_5767512, baseEnd_5767512] using wordTrace_append hprefix tailTrace_5767512
  have hstable : (prefixWord ++ tailWord_5767512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767512).length < 2 ^ (prefixWord ++ tailWord_5767512).sum := by decide
  have hdescent : baseEnd_5767512 < baseStart_5767512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767529 : List Nat := [1, 2, 1, 1, 1, 3, 7, 2, 5]
def baseStart_5767529 : Nat := 118140960795 + 5767529 * 2 ^ 59
def prefixEnd_5767529 : Nat := 4983230072969 + 3 ^ 40 * 5767529 * 2
def baseEnd_5767529 : Nat := 329057173971696694440347

theorem tailTrace_5767529 : CollatzResearch.WordTrace tailWord_5767529 prefixEnd_5767529 329057173971696694440347 := by
  unfold tailWord_5767529
  simp only [CollatzResearch.WordTrace]
  refine ⟨210359064322234923377217641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140239376214823282251478427 210359064322234923377217641)
  ·
    refine ⟨157769298241676192532913231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210359064322234923377217641 157769298241676192532913231)
    ·
      refine ⟨236653947362514288799369847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157769298241676192532913231 236653947362514288799369847)
      ·
        refine ⟨354980921043771433199054771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236653947362514288799369847 354980921043771433199054771)
        ·
          refine ⟨532471381565657149798582157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354980921043771433199054771 532471381565657149798582157)
          ·
            refine ⟨199676768087121431174468309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 532471381565657149798582157 199676768087121431174468309)
            ·
              refine ⟨4679924252041908543151601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 199676768087121431174468309 4679924252041908543151601)
              ·
                refine ⟨3509943189031431407363701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4679924252041908543151601 3509943189031431407363701)
                ·
                  refine ⟨329057173971696694440347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3509943189031431407363701 329057173971696694440347)
                  ·
                    rfl

theorem cell23_5767529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 5].length) (baseStart_5767529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767529 prefixEnd_5767529 := by exact prefixLift 5767529
  have htrace : WordTrace (prefixWord ++ tailWord_5767529) baseStart_5767529 baseEnd_5767529 := by
    simpa [prefixWord, tailWord_5767529, baseEnd_5767529] using wordTrace_append hprefix tailTrace_5767529
  have hstable : (prefixWord ++ tailWord_5767529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767529).length < 2 ^ (prefixWord ++ tailWord_5767529).sum := by decide
  have hdescent : baseEnd_5767529 < baseStart_5767529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767574 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5767574 : Nat := 118140960795 + 5767574 * 2 ^ 59
def prefixEnd_5767574 : Nat := 4983230072969 + 3 ^ 40 * 5767574 * 2
def baseEnd_5767574 : Nat := 2961537672374722573900417

theorem tailTrace_5767574 : CollatzResearch.WordTrace tailWord_5767574 prefixEnd_5767574 2961537672374722573900417 := by
  unfold tailWord_5767574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147544100441993503912861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140240470404714597375070517 13147544100441993503912861)
  ·
    refine ⟨4930329037665747563967323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13147544100441993503912861 4930329037665747563967323)
    ·
      refine ⟨7395493556498621345950985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4930329037665747563967323 7395493556498621345950985)
      ·
        refine ⟨5546620167373966009463239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7395493556498621345950985 5546620167373966009463239)
        ·
          refine ⟨8319930251060949014194859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5546620167373966009463239 8319930251060949014194859)
          ·
            refine ⟨12479895376591423521292289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8319930251060949014194859 12479895376591423521292289)
            ·
              refine ⟨9359921532443567640969217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12479895376591423521292289 9359921532443567640969217)
              ·
                refine ⟨7019941149332675730726913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9359921532443567640969217 7019941149332675730726913)
                ·
                  refine ⟨5264955861999506798045185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7019941149332675730726913 5264955861999506798045185)
                  ·
                    refine ⟨3948716896499630098533889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5264955861999506798045185 3948716896499630098533889)
                    ·
                      refine ⟨2961537672374722573900417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948716896499630098533889 2961537672374722573900417)
                      ·
                        rfl

theorem cell23_5767574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5767574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767574 prefixEnd_5767574 := by exact prefixLift 5767574
  have htrace : WordTrace (prefixWord ++ tailWord_5767574) baseStart_5767574 baseEnd_5767574 := by
    simpa [prefixWord, tailWord_5767574, baseEnd_5767574] using wordTrace_append hprefix tailTrace_5767574
  have hstable : (prefixWord ++ tailWord_5767574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767574).length < 2 ^ (prefixWord ++ tailWord_5767574).sum := by decide
  have hdescent : baseEnd_5767574 < baseStart_5767574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767602 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 6]
def baseStart_5767602 : Nat := 118140960795 + 5767602 * 2 ^ 59
def prefixEnd_5767602 : Nat := 4983230072969 + 3 ^ 40 * 5767602 * 2
def baseEnd_5767602 : Nat := 329061338870338718261143

theorem tailTrace_5767602 : CollatzResearch.WordTrace tailWord_5767602 prefixEnd_5767602 329061338870338718261143 := by
  unfold tailWord_5767602
  simp only [CollatzResearch.WordTrace]
  refine ⟨52590431712742614211156265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140241151233980304563083373 52590431712742614211156265)
  ·
    refine ⟨39442823784556960658367199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52590431712742614211156265 39442823784556960658367199)
    ·
      refine ⟨59164235676835440987550799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39442823784556960658367199 59164235676835440987550799)
      ·
        refine ⟨88746353515253161481326199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59164235676835440987550799 88746353515253161481326199)
        ·
          refine ⟨133119530272879742221989299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88746353515253161481326199 133119530272879742221989299)
          ·
            refine ⟨199679295409319613332983949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133119530272879742221989299 199679295409319613332983949)
            ·
              refine ⟨74879735778494854999868981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199679295409319613332983949 74879735778494854999868981)
              ·
                refine ⟨7019975229233892656237717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74879735778494854999868981 7019975229233892656237717)
                ·
                  refine ⟨329061338870338718261143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7019975229233892656237717 329061338870338718261143)
                  ·
                    rfl

theorem cell23_5767602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_5767602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767602 prefixEnd_5767602 := by exact prefixLift 5767602
  have htrace : WordTrace (prefixWord ++ tailWord_5767602) baseStart_5767602 baseEnd_5767602 := by
    simpa [prefixWord, tailWord_5767602, baseEnd_5767602] using wordTrace_append hprefix tailTrace_5767602
  have hstable : (prefixWord ++ tailWord_5767602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767602).length < 2 ^ (prefixWord ++ tailWord_5767602).sum := by decide
  have hdescent : baseEnd_5767602 < baseStart_5767602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767636 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 6]
def baseStart_5767636 : Nat := 118140960795 + 5767636 * 2 ^ 59
def prefixEnd_5767636 : Nat := 4983230072969 + 3 ^ 40 * 5767636 * 2
def baseEnd_5767636 : Nat := 329063278686144592369459

theorem tailTrace_5767636 : CollatzResearch.WordTrace tailWord_5767636 prefixEnd_5767636 329063278686144592369459 := by
  unfold tailWord_5767636
  simp only [CollatzResearch.WordTrace]
  refine ⟨105181483466423640325681381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140241977955231520434241841 105181483466423640325681381)
  ·
    refine ⟨19721528149954432561065259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105181483466423640325681381 19721528149954432561065259)
    ·
      refine ⟨29582292224931648841597889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19721528149954432561065259 29582292224931648841597889)
      ·
        refine ⟨22186719168698736631198417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29582292224931648841597889 22186719168698736631198417)
        ·
          refine ⟨16640039376524052473398813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22186719168698736631198417 16640039376524052473398813)
          ·
            refine ⟨6240014766196519677524555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16640039376524052473398813 6240014766196519677524555)
            ·
              refine ⟨9360022149294779516286833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6240014766196519677524555 9360022149294779516286833)
              ·
                refine ⟨7020016611971084637215125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9360022149294779516286833 7020016611971084637215125)
                ·
                  refine ⟨329063278686144592369459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7020016611971084637215125 329063278686144592369459)
                  ·
                    rfl

theorem cell23_5767636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_5767636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767636 prefixEnd_5767636 := by exact prefixLift 5767636
  have htrace : WordTrace (prefixWord ++ tailWord_5767636) baseStart_5767636 baseEnd_5767636 := by
    simpa [prefixWord, tailWord_5767636, baseEnd_5767636] using wordTrace_append hprefix tailTrace_5767636
  have hstable : (prefixWord ++ tailWord_5767636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767636).length < 2 ^ (prefixWord ++ tailWord_5767636).sum := by decide
  have hdescent : baseEnd_5767636 < baseStart_5767636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767672 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_5767672 : Nat := 118140960795 + 5767672 * 2 ^ 59
def prefixEnd_5767672 : Nat := 4983230072969 + 3 ^ 40 * 5767672 * 2
def baseEnd_5767672 : Nat := 2961587993478863190474965

theorem tailTrace_5767672 : CollatzResearch.WordTrace tailWord_5767672 prefixEnd_5767672 2961587993478863190474965 := by
  unfold tailWord_5767672
  simp only [CollatzResearch.WordTrace]
  refine ⟨105182139980358429399836635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140242853307144572533115513 105182139980358429399836635)
  ·
    refine ⟨157773209970537644099754953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105182139980358429399836635 157773209970537644099754953)
    ·
      refine ⟨118329907477903233074816215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157773209970537644099754953 118329907477903233074816215)
      ·
        refine ⟨177494861216854849612224323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118329907477903233074816215 177494861216854849612224323)
        ·
          refine ⟨266242291825282274418336485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177494861216854849612224323 266242291825282274418336485)
          ·
            refine ⟨49920429717240426453438091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266242291825282274418336485 49920429717240426453438091)
            ·
              refine ⟨74880644575860639680157137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49920429717240426453438091 74880644575860639680157137)
              ·
                refine ⟨56160483431895479760117853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74880644575860639680157137 56160483431895479760117853)
                ·
                  refine ⟨21060181286960804910044195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56160483431895479760117853 21060181286960804910044195)
                  ·
                    refine ⟨31590271930441207365066293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21060181286960804910044195 31590271930441207365066293)
                    ·
                      refine ⟨2961587993478863190474965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31590271930441207365066293 2961587993478863190474965)
                      ·
                        rfl

theorem cell23_5767672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_5767672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767672 prefixEnd_5767672 := by exact prefixLift 5767672
  have htrace : WordTrace (prefixWord ++ tailWord_5767672) baseStart_5767672 baseEnd_5767672 := by
    simpa [prefixWord, tailWord_5767672, baseEnd_5767672] using wordTrace_append hprefix tailTrace_5767672
  have hstable : (prefixWord ++ tailWord_5767672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767672).length < 2 ^ (prefixWord ++ tailWord_5767672).sum := by decide
  have hdescent : baseEnd_5767672 < baseStart_5767672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767692 : List Nat := [2, 2, 1, 2, 4, 1, 11]
def baseStart_5767692 : Nat := 118140960795 + 5767692 * 2 ^ 59
def prefixEnd_5767692 : Nat := 4983230072969 + 3 ^ 40 * 5767692 * 2
def baseEnd_5767692 : Nat := 36562941519653742126233

theorem tailTrace_5767692 : CollatzResearch.WordTrace tailWord_5767692 prefixEnd_5767692 36562941519653742126233 := by
  unfold tailWord_5767692
  simp only [CollatzResearch.WordTrace]
  refine ⟨105182504710322201107700665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140243339613762934810267553 105182504710322201107700665)
  ·
    refine ⟨78886878532741650830775499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105182504710322201107700665 78886878532741650830775499)
    ·
      refine ⟨118330317799112476246163249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78886878532741650830775499 118330317799112476246163249)
      ·
        refine ⟨88747738349334357184622437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118330317799112476246163249 88747738349334357184622437)
        ·
          refine ⟨16640200940500191972116707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88747738349334357184622437 16640200940500191972116707)
          ·
            refine ⟨24960301410750287958175061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16640200940500191972116707 24960301410750287958175061)
            ·
              refine ⟨36562941519653742126233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24960301410750287958175061 36562941519653742126233)
              ·
                rfl

theorem cell23_5767692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 11].length) (baseStart_5767692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767692 prefixEnd_5767692 := by exact prefixLift 5767692
  have htrace : WordTrace (prefixWord ++ tailWord_5767692) baseStart_5767692 baseEnd_5767692 := by
    simpa [prefixWord, tailWord_5767692, baseEnd_5767692] using wordTrace_append hprefix tailTrace_5767692
  have hstable : (prefixWord ++ tailWord_5767692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767692).length < 2 ^ (prefixWord ++ tailWord_5767692).sum := by decide
  have hdescent : baseEnd_5767692 < baseStart_5767692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767709 : List Nat := [1, 4, 2, 2, 1, 3, 2, 8]
def baseStart_5767709 : Nat := 118140960795 + 5767709 * 2 ^ 59
def prefixEnd_5767709 : Nat := 4983230072969 + 3 ^ 40 * 5767709 * 2
def baseEnd_5767709 : Nat := 109689147861595538730085

theorem tailTrace_5767709 : CollatzResearch.WordTrace tailWord_5767709 prefixEnd_5767709 109689147861595538730085 := by
  unfold tailWord_5767709
  simp only [CollatzResearch.WordTrace]
  refine ⟨210365629461582814118770181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140243752974388542745846787 210365629461582814118770181)
  ·
    refine ⟨39443555524046777647269409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210365629461582814118770181 39443555524046777647269409)
    ·
      refine ⟨29582666643035083235452057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39443555524046777647269409 29582666643035083235452057)
      ·
        refine ⟨22186999982276312426589043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29582666643035083235452057 22186999982276312426589043)
        ·
          refine ⟨33280499973414468639883565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22186999982276312426589043 33280499973414468639883565)
          ·
            refine ⟨12480187490030425739956337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33280499973414468639883565 12480187490030425739956337)
            ·
              refine ⟨9360140617522819304967253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12480187490030425739956337 9360140617522819304967253)
              ·
                refine ⟨109689147861595538730085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9360140617522819304967253 109689147861595538730085)
                ·
                  rfl

theorem cell23_5767709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 8].length) (baseStart_5767709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767709 prefixEnd_5767709 := by exact prefixLift 5767709
  have htrace : WordTrace (prefixWord ++ tailWord_5767709) baseStart_5767709 baseEnd_5767709 := by
    simpa [prefixWord, tailWord_5767709, baseEnd_5767709] using wordTrace_append hprefix tailTrace_5767709
  have hstable : (prefixWord ++ tailWord_5767709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767709).length < 2 ^ (prefixWord ++ tailWord_5767709).sum := by decide
  have hdescent : baseEnd_5767709 < baseStart_5767709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767748 : List Nat := [2, 3, 5, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5767748 : Nat := 118140960795 + 5767748 * 2 ^ 59
def prefixEnd_5767748 : Nat := 4983230072969 + 3 ^ 40 * 5767748 * 2
def baseEnd_5767748 : Nat := 2961627018008604893124617

theorem tailTrace_5767748 : CollatzResearch.WordTrace tailWord_5767748 prefixEnd_5767748 2961627018008604893124617 := by
  unfold tailWord_5767748
  simp only [CollatzResearch.WordTrace]
  refine ⟨105183525954220761889719949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140244701272294349186293265 105183525954220761889719949)
  ·
    refine ⟨39443822232832785708644981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105183525954220761889719949 39443822232832785708644981)
    ·
      refine ⟨3697858334328073660185467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39443822232832785708644981 3697858334328073660185467)
      ·
        refine ⟨5546787501492110490278201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3697858334328073660185467 5546787501492110490278201)
        ·
          refine ⟨4160090626119082867708651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5546787501492110490278201 4160090626119082867708651)
          ·
            refine ⟨6240135939178624301562977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160090626119082867708651 6240135939178624301562977)
            ·
              refine ⟨4680101954383968226172233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6240135939178624301562977 4680101954383968226172233)
              ·
                refine ⟨3510076465787976169629175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4680101954383968226172233 3510076465787976169629175)
                ·
                  refine ⟨5265114698681964254443763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510076465787976169629175 5265114698681964254443763)
                  ·
                    refine ⟨7897672048022946381665645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5265114698681964254443763 7897672048022946381665645)
                    ·
                      refine ⟨2961627018008604893124617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7897672048022946381665645 2961627018008604893124617)
                      ·
                        rfl

theorem cell23_5767748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5767748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767748 prefixEnd_5767748 := by exact prefixLift 5767748
  have htrace : WordTrace (prefixWord ++ tailWord_5767748) baseStart_5767748 baseEnd_5767748 := by
    simpa [prefixWord, tailWord_5767748, baseEnd_5767748] using wordTrace_append hprefix tailTrace_5767748
  have hstable : (prefixWord ++ tailWord_5767748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767748).length < 2 ^ (prefixWord ++ tailWord_5767748).sum := by decide
  have hdescent : baseEnd_5767748 < baseStart_5767748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767752 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 3, 8]
def baseStart_5767752 : Nat := 118140960795 + 5767752 * 2 ^ 59
def prefixEnd_5767752 : Nat := 4983230072969 + 3 ^ 40 * 5767752 * 2
def baseEnd_5767752 : Nat := 987209690643740959158199

theorem tailTrace_5767752 : CollatzResearch.WordTrace tailWord_5767752 prefixEnd_5767752 987209690643740959158199 := by
  unfold tailWord_5767752
  simp only [CollatzResearch.WordTrace]
  refine ⟨105183598900213516231292755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140244798533618021641723673 105183598900213516231292755)
  ·
    refine ⟨157775398350320274346939133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105183598900213516231292755 157775398350320274346939133)
    ·
      refine ⟨59165774381370102880102175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157775398350320274346939133 59165774381370102880102175)
      ·
        refine ⟨88748661572055154320153263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59165774381370102880102175 88748661572055154320153263)
        ·
          refine ⟨133122992358082731480229895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88748661572055154320153263 133122992358082731480229895)
          ·
            refine ⟨199684488537124097220344843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133122992358082731480229895 199684488537124097220344843)
            ·
              refine ⟨299526732805686145830517265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199684488537124097220344843 299526732805686145830517265)
              ·
                refine ⟨224645049604264609372887949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299526732805686145830517265 224645049604264609372887949)
                ·
                  refine ⟨84241893601599228514832981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224645049604264609372887949 84241893601599228514832981)
                  ·
                    refine ⟨987209690643740959158199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84241893601599228514832981 987209690643740959158199)
                    ·
                      rfl

theorem cell23_5767752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_5767752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767752 prefixEnd_5767752 := by exact prefixLift 5767752
  have htrace : WordTrace (prefixWord ++ tailWord_5767752) baseStart_5767752 baseEnd_5767752 := by
    simpa [prefixWord, tailWord_5767752, baseEnd_5767752] using wordTrace_append hprefix tailTrace_5767752
  have hstable : (prefixWord ++ tailWord_5767752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767752).length < 2 ^ (prefixWord ++ tailWord_5767752).sum := by decide
  have hdescent : baseEnd_5767752 < baseStart_5767752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767776 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 1, 4, 2]
def baseStart_5767776 : Nat := 118140960795 + 5767776 * 2 ^ 59
def prefixEnd_5767776 : Nat := 4983230072969 + 3 ^ 40 * 5767776 * 2
def baseEnd_5767776 : Nat := 2961641395466930783574487

theorem tailTrace_5767776 : CollatzResearch.WordTrace tailWord_5767776 prefixEnd_5767776 2961641395466930783574487 := by
  unfold tailWord_5767776
  simp only [CollatzResearch.WordTrace]
  refine ⟨105184036576170042280729591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140245382101560056374306121 105184036576170042280729591)
  ·
    refine ⟨157776054864255063421094387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105184036576170042280729591 157776054864255063421094387)
    ·
      refine ⟨236664082296382595131641581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157776054864255063421094387 236664082296382595131641581)
      ·
        refine ⟨88749030861143473174365593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236664082296382595131641581 88749030861143473174365593)
        ·
          refine ⟨66561773145857604880774195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88749030861143473174365593 66561773145857604880774195)
          ·
            refine ⟨99842659718786407321161293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66561773145857604880774195 99842659718786407321161293)
            ·
              refine ⟨37440997394544902745435485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99842659718786407321161293 37440997394544902745435485)
              ·
                refine ⟨14040374022954338529538307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37440997394544902745435485 14040374022954338529538307)
                ·
                  refine ⟨21060561034431507794307461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14040374022954338529538307 21060561034431507794307461)
                  ·
                    refine ⟨3948855193955907711432649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21060561034431507794307461 3948855193955907711432649)
                    ·
                      refine ⟨2961641395466930783574487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948855193955907711432649 2961641395466930783574487)
                      ·
                        rfl

theorem cell23_5767776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_5767776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767776 prefixEnd_5767776 := by exact prefixLift 5767776
  have htrace : WordTrace (prefixWord ++ tailWord_5767776) baseStart_5767776 baseEnd_5767776 := by
    simpa [prefixWord, tailWord_5767776, baseEnd_5767776] using wordTrace_append hprefix tailTrace_5767776
  have hstable : (prefixWord ++ tailWord_5767776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767776).length < 2 ^ (prefixWord ++ tailWord_5767776).sum := by decide
  have hdescent : baseEnd_5767776 < baseStart_5767776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767779 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 3]
def baseStart_5767779 : Nat := 118140960795 + 5767779 * 2 ^ 59
def prefixEnd_5767779 : Nat := 4983230072969 + 3 ^ 40 * 5767779 * 2
def baseEnd_5767779 : Nat := 2961642935908894271836973

theorem tailTrace_5767779 : CollatzResearch.WordTrace tailWord_5767779 prefixEnd_5767779 2961642935908894271836973 := by
  unfold tailWord_5767779
  simp only [CollatzResearch.WordTrace]
  refine ⟨210368182571329216073818391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140245455047552810715878927 210368182571329216073818391)
  ·
    refine ⟨315552273856993824110727587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210368182571329216073818391 315552273856993824110727587)
    ·
      refine ⟨473328410785490736166091381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315552273856993824110727587 473328410785490736166091381)
      ·
        refine ⟨44374538511139756515571067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 473328410785490736166091381 44374538511139756515571067)
        ·
          refine ⟨66561807766709634773356601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44374538511139756515571067 66561807766709634773356601)
          ·
            refine ⟨49921355825032226080017451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66561807766709634773356601 49921355825032226080017451)
            ·
              refine ⟨74882033737548339120026177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49921355825032226080017451 74882033737548339120026177)
              ·
                refine ⟨56161525303161254340019633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74882033737548339120026177 56161525303161254340019633)
                ·
                  refine ⟨42121143977370940755014725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56161525303161254340019633 42121143977370940755014725)
                  ·
                    refine ⟨7897714495757051391565261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42121143977370940755014725 7897714495757051391565261)
                    ·
                      refine ⟨2961642935908894271836973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7897714495757051391565261 2961642935908894271836973)
                      ·
                        rfl

theorem cell23_5767779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_5767779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767779 prefixEnd_5767779 := by exact prefixLift 5767779
  have htrace : WordTrace (prefixWord ++ tailWord_5767779) baseStart_5767779 baseEnd_5767779 := by
    simpa [prefixWord, tailWord_5767779, baseEnd_5767779] using wordTrace_append hprefix tailTrace_5767779
  have hstable : (prefixWord ++ tailWord_5767779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767779).length < 2 ^ (prefixWord ++ tailWord_5767779).sum := by decide
  have hdescent : baseEnd_5767779 < baseStart_5767779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767866 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_5767866 : Nat := 118140960795 + 5767866 * 2 ^ 59
def prefixEnd_5767866 : Nat := 4983230072969 + 3 ^ 40 * 5767866 * 2
def baseEnd_5767866 : Nat := 2961687608725835431449073

theorem tailTrace_5767866 : CollatzResearch.WordTrace tailWord_5767866 prefixEnd_5767866 2961687608725835431449073 := by
  unfold tailWord_5767866
  simp only [CollatzResearch.WordTrace]
  refine ⟨52592838930503507483058863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140247570481342686621490301 52592838930503507483058863)
  ·
    refine ⟨78889258395755261224588295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52592838930503507483058863 78889258395755261224588295)
    ·
      refine ⟨118333887593632891836882443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78889258395755261224588295 118333887593632891836882443)
      ·
        refine ⟨177500831390449337755323665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118333887593632891836882443 177500831390449337755323665)
        ·
          refine ⟨133125623542837003316492749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177500831390449337755323665 133125623542837003316492749)
          ·
            refine ⟨49922108828563876243684781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133125623542837003316492749 49922108828563876243684781)
            ·
              refine ⟨18720790810711453591381793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49922108828563876243684781 18720790810711453591381793)
              ·
                refine ⟨14040593108033590193536345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18720790810711453591381793 14040593108033590193536345)
                ·
                  refine ⟨10530444831025192645152259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14040593108033590193536345 10530444831025192645152259)
                  ·
                    refine ⟨15795667246537788967728389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10530444831025192645152259 15795667246537788967728389)
                    ·
                      refine ⟨2961687608725835431449073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15795667246537788967728389 2961687608725835431449073)
                      ·
                        rfl

theorem cell23_5767866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_5767866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767866 prefixEnd_5767866 := by exact prefixLift 5767866
  have htrace : WordTrace (prefixWord ++ tailWord_5767866) baseStart_5767866 baseEnd_5767866 := by
    simpa [prefixWord, tailWord_5767866, baseEnd_5767866] using wordTrace_append hprefix tailTrace_5767866
  have hstable : (prefixWord ++ tailWord_5767866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767866).length < 2 ^ (prefixWord ++ tailWord_5767866).sum := by decide
  have hdescent : baseEnd_5767866 < baseStart_5767866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767878 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5767878 : Nat := 118140960795 + 5767878 * 2 ^ 59
def prefixEnd_5767878 : Nat := 4983230072969 + 3 ^ 40 * 5767878 * 2
def baseEnd_5767878 : Nat := 2961693770493689384499019

theorem tailTrace_5767878 : CollatzResearch.WordTrace tailWord_5767878 prefixEnd_5767878 2961693770493689384499019 := by
  unfold tailWord_5767878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574118543686579874427259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140247862265313703987781525 6574118543686579874427259)
  ·
    refine ⟨9861177815529869811640889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6574118543686579874427259 9861177815529869811640889)
    ·
      refine ⟨7395883361647402358730667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9861177815529869811640889 7395883361647402358730667)
      ·
        refine ⟨11093825042471103538096001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395883361647402358730667 11093825042471103538096001)
        ·
          refine ⟨8320368781853327653572001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11093825042471103538096001 8320368781853327653572001)
          ·
            refine ⟨6240276586389995740179001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8320368781853327653572001 6240276586389995740179001)
            ·
              refine ⟨4680207439792496805134251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6240276586389995740179001 4680207439792496805134251)
              ·
                refine ⟨7020311159688745207701377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680207439792496805134251 7020311159688745207701377)
                ·
                  refine ⟨5265233369766558905776033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7020311159688745207701377 5265233369766558905776033)
                  ·
                    refine ⟨3948925027324919179332025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5265233369766558905776033 3948925027324919179332025)
                    ·
                      refine ⟨2961693770493689384499019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3948925027324919179332025 2961693770493689384499019)
                      ·
                        rfl

theorem cell23_5767878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5767878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767878 prefixEnd_5767878 := by exact prefixLift 5767878
  have htrace : WordTrace (prefixWord ++ tailWord_5767878) baseStart_5767878 baseEnd_5767878 := by
    simpa [prefixWord, tailWord_5767878, baseEnd_5767878] using wordTrace_append hprefix tailTrace_5767878
  have hstable : (prefixWord ++ tailWord_5767878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767878).length < 2 ^ (prefixWord ++ tailWord_5767878).sum := by decide
  have hdescent : baseEnd_5767878 < baseStart_5767878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767879 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_5767879 : Nat := 118140960795 + 5767879 * 2 ^ 59
def prefixEnd_5767879 : Nat := 4983230072969 + 3 ^ 40 * 5767879 * 2
def baseEnd_5767879 : Nat := 2961694283974343880586513

theorem tailTrace_5767879 : CollatzResearch.WordTrace tailWord_5767879 prefixEnd_5767879 2961694283974343880586513 := by
  unfold tailWord_5767879
  simp only [CollatzResearch.WordTrace]
  refine ⟨210371829870966933152458691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140247886580644622101639127 210371829870966933152458691)
  ·
    refine ⟨315557744806450399728688037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210371829870966933152458691 315557744806450399728688037)
    ·
      refine ⟨59167077151209449949129007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315557744806450399728688037 59167077151209449949129007)
      ·
        refine ⟨88750615726814174923693511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59167077151209449949129007 88750615726814174923693511)
        ·
          refine ⟨133125923590221262385540267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88750615726814174923693511 133125923590221262385540267)
          ·
            refine ⟨199688885385331893578310401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133125923590221262385540267 199688885385331893578310401)
            ·
              refine ⟨149766664038998920183732801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199688885385331893578310401 149766664038998920183732801)
              ·
                refine ⟨112324998029249190137799601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149766664038998920183732801 112324998029249190137799601)
                ·
                  refine ⟨84243748521936892603349701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112324998029249190137799601 84243748521936892603349701)
                  ·
                    refine ⟨15795702847863167363128069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84243748521936892603349701 15795702847863167363128069)
                    ·
                      refine ⟨2961694283974343880586513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15795702847863167363128069 2961694283974343880586513)
                      ·
                        rfl

theorem cell23_5767879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_5767879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767879 prefixEnd_5767879 := by exact prefixLift 5767879
  have htrace : WordTrace (prefixWord ++ tailWord_5767879) baseStart_5767879 baseEnd_5767879 := by
    simpa [prefixWord, tailWord_5767879, baseEnd_5767879] using wordTrace_append hprefix tailTrace_5767879
  have hstable : (prefixWord ++ tailWord_5767879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767879).length < 2 ^ (prefixWord ++ tailWord_5767879).sum := by decide
  have hdescent : baseEnd_5767879 < baseStart_5767879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767900 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_5767900 : Nat := 118140960795 + 5767900 * 2 ^ 59
def prefixEnd_5767900 : Nat := 4983230072969 + 3 ^ 40 * 5767900 * 2
def baseEnd_5767900 : Nat := 2961705067068088298423917

theorem tailTrace_5767900 : CollatzResearch.WordTrace tailWord_5767900 prefixEnd_5767900 2961705067068088298423917 := by
  unfold tailWord_5767900
  simp only [CollatzResearch.WordTrace]
  refine ⟨105186297901945426869486577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140248397202593902492648769 105186297901945426869486577)
  ·
    refine ⟨78889723426459070152114933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105186297901945426869486577 78889723426459070152114933)
    ·
      refine ⟨7395911571230537826760775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78889723426459070152114933 7395911571230537826760775)
      ·
        refine ⟨11093867356845806740141163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395911571230537826760775 11093867356845806740141163)
        ·
          refine ⟨16640801035268710110211745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11093867356845806740141163 16640801035268710110211745)
          ·
            refine ⟨12480600776451532582658809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16640801035268710110211745 12480600776451532582658809)
            ·
              refine ⟨9360450582338649436994107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12480600776451532582658809 9360450582338649436994107)
              ·
                refine ⟨14040675873507974155491161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9360450582338649436994107 14040675873507974155491161)
                ·
                  refine ⟨10530506905130980616618371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14040675873507974155491161 10530506905130980616618371)
                  ·
                    refine ⟨15795760357696470924927557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10530506905130980616618371 15795760357696470924927557)
                    ·
                      refine ⟨2961705067068088298423917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15795760357696470924927557 2961705067068088298423917)
                      ·
                        rfl

theorem cell23_5767900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_5767900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767900 prefixEnd_5767900 := by exact prefixLift 5767900
  have htrace : WordTrace (prefixWord ++ tailWord_5767900) baseStart_5767900 baseEnd_5767900 := by
    simpa [prefixWord, tailWord_5767900, baseEnd_5767900] using wordTrace_append hprefix tailTrace_5767900
  have hstable : (prefixWord ++ tailWord_5767900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767900).length < 2 ^ (prefixWord ++ tailWord_5767900).sum := by decide
  have hdescent : baseEnd_5767900 < baseStart_5767900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767903 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 3]
def baseStart_5767903 : Nat := 118140960795 + 5767903 * 2 ^ 59
def prefixEnd_5767903 : Nat := 4983230072969 + 3 ^ 40 * 5767903 * 2
def baseEnd_5767903 : Nat := 2961706607510051786686403

theorem tailTrace_5767903 : CollatzResearch.WordTrace tailWord_5767903 prefixEnd_5767903 2961706607510051786686403 := by
  unfold tailWord_5767903
  simp only [CollatzResearch.WordTrace]
  refine ⟨210372705222879985251332363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140248470148586656834221575 210372705222879985251332363)
  ·
    refine ⟨315559057834319977876998545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210372705222879985251332363 315559057834319977876998545)
    ·
      refine ⟨236669293375739983407748909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315559057834319977876998545 236669293375739983407748909)
      ·
        refine ⟨88750985015902493777905841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236669293375739983407748909 88750985015902493777905841)
        ·
          refine ⟨66563238761926870333429381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88750985015902493777905841 66563238761926870333429381)
          ·
            refine ⟨12480607267861288187518009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66563238761926870333429381 12480607267861288187518009)
            ·
              refine ⟨9360455450895966140638507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12480607267861288187518009 9360455450895966140638507)
              ·
                refine ⟨14040683176343949210957761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9360455450895966140638507 14040683176343949210957761)
                ·
                  refine ⟨10530512382257961908218321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14040683176343949210957761 10530512382257961908218321)
                  ·
                    refine ⟨7897884286693471431163741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10530512382257961908218321 7897884286693471431163741)
                    ·
                      refine ⟨2961706607510051786686403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7897884286693471431163741 2961706607510051786686403)
                      ·
                        rfl

theorem cell23_5767903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_5767903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767903 prefixEnd_5767903 := by exact prefixLift 5767903
  have htrace : WordTrace (prefixWord ++ tailWord_5767903) baseStart_5767903 baseEnd_5767903 := by
    simpa [prefixWord, tailWord_5767903, baseEnd_5767903] using wordTrace_append hprefix tailTrace_5767903
  have hstable : (prefixWord ++ tailWord_5767903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767903).length < 2 ^ (prefixWord ++ tailWord_5767903).sum := by decide
  have hdescent : baseEnd_5767903 < baseStart_5767903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767926 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_5767926 : Nat := 118140960795 + 5767926 * 2 ^ 59
def prefixEnd_5767926 : Nat := 4983230072969 + 3 ^ 40 * 5767926 * 2
def baseEnd_5767926 : Nat := 2961718417565105196698797

theorem tailTrace_5767926 : CollatzResearch.WordTrace tailWord_5767926 prefixEnd_5767926 2961718417565105196698797 := by
  unfold tailWord_5767926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13148346506362291261213727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140249029401197773452946421 13148346506362291261213727)
  ·
    refine ⟨19722519759543436891820591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13148346506362291261213727 19722519759543436891820591)
    ·
      refine ⟨29583779639315155337730887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19722519759543436891820591 29583779639315155337730887)
      ·
        refine ⟨44375669458972733006596331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29583779639315155337730887 44375669458972733006596331)
        ·
          refine ⟨66563504188459099509894497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44375669458972733006596331 66563504188459099509894497)
          ·
            refine ⟨49922628141344324632420873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66563504188459099509894497 49922628141344324632420873)
            ·
              refine ⟨37441971106008243474315655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49922628141344324632420873 37441971106008243474315655)
              ·
                refine ⟨56162956659012365211473483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37441971106008243474315655 56162956659012365211473483)
                ·
                  refine ⟨84244434988518547817210225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56162956659012365211473483 84244434988518547817210225)
                  ·
                    refine ⟨63183326241388910862907669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84244434988518547817210225 63183326241388910862907669)
                    ·
                      refine ⟨2961718417565105196698797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63183326241388910862907669 2961718417565105196698797)
                      ·
                        rfl

theorem cell23_5767926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_5767926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767926 prefixEnd_5767926 := by exact prefixLift 5767926
  have htrace : WordTrace (prefixWord ++ tailWord_5767926) baseStart_5767926 baseEnd_5767926 := by
    simpa [prefixWord, tailWord_5767926, baseEnd_5767926] using wordTrace_append hprefix tailTrace_5767926
  have hstable : (prefixWord ++ tailWord_5767926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767926).length < 2 ^ (prefixWord ++ tailWord_5767926).sum := by decide
  have hdescent : baseEnd_5767926 < baseStart_5767926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767929 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_5767929 : Nat := 118140960795 + 5767929 * 2 ^ 59
def prefixEnd_5767929 : Nat := 4983230072969 + 3 ^ 40 * 5767929 * 2
def baseEnd_5767929 : Nat := 2961719958007068684961283

theorem tailTrace_5767929 : CollatzResearch.WordTrace tailWord_5767929 prefixEnd_5767929 2961719958007068684961283 := by
  unfold tailWord_5767929
  simp only [CollatzResearch.WordTrace]
  refine ⟨210373653520785791691778841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140249102347190527794519227 210373653520785791691778841)
  ·
    refine ⟨157780240140589343768834131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210373653520785791691778841 157780240140589343768834131)
    ·
      refine ⟨236670360210884015653251197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157780240140589343768834131 236670360210884015653251197)
      ·
        refine ⟨88751385079081505869969199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236670360210884015653251197 88751385079081505869969199)
        ·
          refine ⟨133127077618622258804953799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88751385079081505869969199 133127077618622258804953799)
          ·
            refine ⟨199690616427933388207430699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133127077618622258804953799 199690616427933388207430699)
            ·
              refine ⟨299535924641900082311146049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199690616427933388207430699 299535924641900082311146049)
              ·
                refine ⟨224651943481425061733359537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299535924641900082311146049 224651943481425061733359537)
                ·
                  refine ⟨168488957611068796300019653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224651943481425061733359537 168488957611068796300019653)
                  ·
                    refine ⟨31591679552075399306253685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168488957611068796300019653 31591679552075399306253685)
                    ·
                      refine ⟨2961719958007068684961283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31591679552075399306253685 2961719958007068684961283)
                      ·
                        rfl

theorem cell23_5767929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_5767929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767929 prefixEnd_5767929 := by exact prefixLift 5767929
  have htrace : WordTrace (prefixWord ++ tailWord_5767929) baseStart_5767929 baseEnd_5767929 := by
    simpa [prefixWord, tailWord_5767929, baseEnd_5767929] using wordTrace_append hprefix tailTrace_5767929
  have hstable : (prefixWord ++ tailWord_5767929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767929).length < 2 ^ (prefixWord ++ tailWord_5767929).sum := by decide
  have hdescent : baseEnd_5767929 < baseStart_5767929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767933 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_5767933 : Nat := 118140960795 + 5767933 * 2 ^ 59
def prefixEnd_5767933 : Nat := 4983230072969 + 3 ^ 40 * 5767933 * 2
def baseEnd_5767933 : Nat := 2961722011929686669311265

theorem tailTrace_5767933 : CollatzResearch.WordTrace tailWord_5767933 prefixEnd_5767933 2961722011929686669311265 := by
  unfold tailWord_5767933
  simp only [CollatzResearch.WordTrace]
  refine ⟨210373799412771300374924453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140249199608514200249949635 210373799412771300374924453)
  ·
    refine ⟨39445087389894618820298335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210373799412771300374924453 39445087389894618820298335)
    ·
      refine ⟨59167631084841928230447503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39445087389894618820298335 59167631084841928230447503)
      ·
        refine ⟨88751446627262892345671255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59167631084841928230447503 88751446627262892345671255)
        ·
          refine ⟨133127169940894338518506883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88751446627262892345671255 133127169940894338518506883)
          ·
            refine ⟨199690754911341507777760325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133127169940894338518506883 199690754911341507777760325)
            ·
              refine ⟨37442016545876532708330061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199690754911341507777760325 37442016545876532708330061)
              ·
                refine ⟨14040756204703699765623773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37442016545876532708330061 14040756204703699765623773)
                ·
                  refine ⟨5265283576763887412108915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14040756204703699765623773 5265283576763887412108915)
                  ·
                    refine ⟨7897925365145831118163373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5265283576763887412108915 7897925365145831118163373)
                    ·
                      refine ⟨2961722011929686669311265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7897925365145831118163373 2961722011929686669311265)
                      ·
                        rfl

theorem cell23_5767933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_5767933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767933 prefixEnd_5767933 := by exact prefixLift 5767933
  have htrace : WordTrace (prefixWord ++ tailWord_5767933) baseStart_5767933 baseEnd_5767933 := by
    simpa [prefixWord, tailWord_5767933, baseEnd_5767933] using wordTrace_append hprefix tailTrace_5767933
  have hstable : (prefixWord ++ tailWord_5767933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767933).length < 2 ^ (prefixWord ++ tailWord_5767933).sum := by decide
  have hdescent : baseEnd_5767933 < baseStart_5767933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767954 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5767954 : Nat := 118140960795 + 5767954 * 2 ^ 59
def prefixEnd_5767954 : Nat := 4983230072969 + 3 ^ 40 * 5767954 * 2
def baseEnd_5767954 : Nat := 2961732795023431087148669

theorem tailTrace_5767954 : CollatzResearch.WordTrace tailWord_5767954 prefixEnd_5767954 2961732795023431087148669 := by
  unfold tailWord_5767954
  simp only [CollatzResearch.WordTrace]
  refine ⟨52593641336423805240359729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140249710230463480640959277 52593641336423805240359729)
  ·
    refine ⟨39445231002317853930269797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52593641336423805240359729 39445231002317853930269797)
    ·
      refine ⟨7395980812934597611925587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39445231002317853930269797 7395980812934597611925587)
      ·
        refine ⟨11093971219401896417888381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395980812934597611925587 11093971219401896417888381)
        ·
          refine ⟨4160239207275711156708143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11093971219401896417888381 4160239207275711156708143)
          ·
            refine ⟨6240358810913566735062215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160239207275711156708143 6240358810913566735062215)
            ·
              refine ⟨9360538216370350102593323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6240358810913566735062215 9360538216370350102593323)
              ·
                refine ⟨14040807324555525153889985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9360538216370350102593323 14040807324555525153889985)
                ·
                  refine ⟨10530605493416643865417489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14040807324555525153889985 10530605493416643865417489)
                  ·
                    refine ⟨7897954120062482899063117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10530605493416643865417489 7897954120062482899063117)
                    ·
                      refine ⟨2961732795023431087148669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7897954120062482899063117 2961732795023431087148669)
                      ·
                        rfl

theorem cell23_5767954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5767954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767954 prefixEnd_5767954 := by exact prefixLift 5767954
  have htrace : WordTrace (prefixWord ++ tailWord_5767954) baseStart_5767954 baseEnd_5767954 := by
    simpa [prefixWord, tailWord_5767954, baseEnd_5767954] using wordTrace_append hprefix tailTrace_5767954
  have hstable : (prefixWord ++ tailWord_5767954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767954).length < 2 ^ (prefixWord ++ tailWord_5767954).sum := by decide
  have hdescent : baseEnd_5767954 < baseStart_5767954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767967 : List Nat := [1, 1, 2, 4, 2, 3, 2, 3, 1, 1, 3]
def baseStart_5767967 : Nat := 118140960795 + 5767967 * 2 ^ 59
def prefixEnd_5767967 : Nat := 4983230072969 + 3 ^ 40 * 5767967 * 2
def baseEnd_5767967 : Nat := 2961739470271939536286109

theorem tailTrace_5767967 : CollatzResearch.WordTrace tailWord_5767967 prefixEnd_5767967 2961739470271939536286109 := by
  unfold tailWord_5767967
  simp only [CollatzResearch.WordTrace]
  refine ⟨210375039494648124181662155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140250026329765416121108103 210375039494648124181662155)
  ·
    refine ⟨315562559241972186272493233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210375039494648124181662155 315562559241972186272493233)
    ·
      refine ⟨236671919431479139704369925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315562559241972186272493233 236671919431479139704369925)
      ·
        refine ⟨44375984893402338694569361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236671919431479139704369925 44375984893402338694569361)
        ·
          refine ⟨33281988670051754020927021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44375984893402338694569361 33281988670051754020927021)
          ·
            refine ⟨12480745751269407757847633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33281988670051754020927021 12480745751269407757847633)
            ·
              refine ⟨9360559313452055818385725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12480745751269407757847633 9360559313452055818385725)
              ·
                refine ⟨3510209742544520931894647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9360559313452055818385725 3510209742544520931894647)
                ·
                  refine ⟨5265314613816781397841971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510209742544520931894647 5265314613816781397841971)
                  ·
                    refine ⟨7897971920725172096762957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5265314613816781397841971 7897971920725172096762957)
                    ·
                      refine ⟨2961739470271939536286109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7897971920725172096762957 2961739470271939536286109)
                      ·
                        rfl

theorem cell23_5767967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_5767967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767967 prefixEnd_5767967 := by exact prefixLift 5767967
  have htrace : WordTrace (prefixWord ++ tailWord_5767967) baseStart_5767967 baseEnd_5767967 := by
    simpa [prefixWord, tailWord_5767967, baseEnd_5767967] using wordTrace_append hprefix tailTrace_5767967
  have hstable : (prefixWord ++ tailWord_5767967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767967).length < 2 ^ (prefixWord ++ tailWord_5767967).sum := by decide
  have hdescent : baseEnd_5767967 < baseStart_5767967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767970 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_5767970 : Nat := 118140960795 + 5767970 * 2 ^ 59
def prefixEnd_5767970 : Nat := 4983230072969 + 3 ^ 40 * 5767970 * 2
def baseEnd_5767970 : Nat := 987247003571301008182865

theorem tailTrace_5767970 : CollatzResearch.WordTrace tailWord_5767970 prefixEnd_5767970 987247003571301008182865 := by
  unfold tailWord_5767970
  simp only [CollatzResearch.WordTrace]
  refine ⟨52593787228409313923505341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140250099275758170462680909 52593787228409313923505341)
  ·
    refine ⟨19722670210653492721314503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52593787228409313923505341 19722670210653492721314503)
    ·
      refine ⟨29584005315980239081971755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19722670210653492721314503 29584005315980239081971755)
      ·
        refine ⟨44376007973970358622957633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29584005315980239081971755 44376007973970358622957633)
        ·
          refine ⟨33282005980477768967218225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44376007973970358622957633 33282005980477768967218225)
          ·
            refine ⟨24961504485358326725413669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33282005980477768967218225 24961504485358326725413669)
            ·
              refine ⟨4680282091004686261015063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24961504485358326725413669 4680282091004686261015063)
              ·
                refine ⟨7020423136507029391522595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680282091004686261015063 7020423136507029391522595)
                ·
                  refine ⟨10530634704760544087283893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7020423136507029391522595 10530634704760544087283893)
                  ·
                    refine ⟨987247003571301008182865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10530634704760544087283893 987247003571301008182865)
                    ·
                      rfl

theorem cell23_5767970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_5767970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767970 prefixEnd_5767970 := by exact prefixLift 5767970
  have htrace : WordTrace (prefixWord ++ tailWord_5767970) baseStart_5767970 baseEnd_5767970 := by
    simpa [prefixWord, tailWord_5767970, baseEnd_5767970] using wordTrace_append hprefix tailTrace_5767970
  have hstable : (prefixWord ++ tailWord_5767970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767970).length < 2 ^ (prefixWord ++ tailWord_5767970).sum := by decide
  have hdescent : baseEnd_5767970 < baseStart_5767970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767973 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_5767973 : Nat := 118140960795 + 5767973 * 2 ^ 59
def prefixEnd_5767973 : Nat := 4983230072969 + 3 ^ 40 * 5767973 * 2
def baseEnd_5767973 : Nat := 2961742551155866512811081

theorem tailTrace_5767973 : CollatzResearch.WordTrace tailWord_5767973 prefixEnd_5767973 2961742551155866512811081 := by
  unfold tailWord_5767973
  simp only [CollatzResearch.WordTrace]
  refine ⟨210375258332626387206380573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140250172221750924804253715 210375258332626387206380573)
  ·
    refine ⟨78890721874734895202392715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210375258332626387206380573 78890721874734895202392715)
    ·
      refine ⟨118336082812102342803589073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78890721874734895202392715 118336082812102342803589073)
      ·
        refine ⟨88752062109076757102691805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118336082812102342803589073 88752062109076757102691805)
        ·
          refine ⟨33282023290903783913509427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88752062109076757102691805 33282023290903783913509427)
          ·
            refine ⟨49923034936355675870264141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33282023290903783913509427 49923034936355675870264141)
            ·
              refine ⟨18721138101133378451349053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49923034936355675870264141 18721138101133378451349053)
              ·
                refine ⟨7020426787925016919255895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18721138101133378451349053 7020426787925016919255895)
                ·
                  refine ⟨10530640181887525378883843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7020426787925016919255895 10530640181887525378883843)
                  ·
                    refine ⟨15795960272831288068325765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10530640181887525378883843 15795960272831288068325765)
                    ·
                      refine ⟨2961742551155866512811081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15795960272831288068325765 2961742551155866512811081)
                      ·
                        rfl

theorem cell23_5767973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_5767973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767973 prefixEnd_5767973 := by exact prefixLift 5767973
  have htrace : WordTrace (prefixWord ++ tailWord_5767973) baseStart_5767973 baseEnd_5767973 := by
    simpa [prefixWord, tailWord_5767973, baseEnd_5767973] using wordTrace_append hprefix tailTrace_5767973
  have hstable : (prefixWord ++ tailWord_5767973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767973).length < 2 ^ (prefixWord ++ tailWord_5767973).sum := by decide
  have hdescent : baseEnd_5767973 < baseStart_5767973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5767986 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_5767986 : Nat := 118140960795 + 5767986 * 2 ^ 59
def prefixEnd_5767986 : Nat := 4983230072969 + 3 ^ 40 * 5767986 * 2
def baseEnd_5767986 : Nat := 2961749226404374961948521

theorem tailTrace_5767986 : CollatzResearch.WordTrace tailWord_5767986 prefixEnd_5767986 2961749226404374961948521 := by
  unfold tailWord_5767986
  simp only [CollatzResearch.WordTrace]
  refine ⟨52593933120394822606650953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140250488321052860284402541 52593933120394822606650953)
  ·
    refine ⟨39445449840296116954988215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52593933120394822606650953 39445449840296116954988215)
    ·
      refine ⟨59168174760444175432482323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39445449840296116954988215 59168174760444175432482323)
      ·
        refine ⟨88752262140666263148723485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59168174760444175432482323 88752262140666263148723485)
        ·
          refine ⟨33282098302749848680771307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88752262140666263148723485 33282098302749848680771307)
          ·
            refine ⟨49923147454124773021156961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33282098302749848680771307 49923147454124773021156961)
            ·
              refine ⟨37442360590593579765867721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49923147454124773021156961 37442360590593579765867721)
              ·
                refine ⟨28081770442945184824400791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37442360590593579765867721 28081770442945184824400791)
                ·
                  refine ⟨42122655664417777236601187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28081770442945184824400791 42122655664417777236601187)
                  ·
                    refine ⟨63183983496626665854901781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42122655664417777236601187 63183983496626665854901781)
                    ·
                      refine ⟨2961749226404374961948521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63183983496626665854901781 2961749226404374961948521)
                      ·
                        rfl

theorem cell23_5767986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_5767986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5767986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5767986 prefixEnd_5767986 := by exact prefixLift 5767986
  have htrace : WordTrace (prefixWord ++ tailWord_5767986) baseStart_5767986 baseEnd_5767986 := by
    simpa [prefixWord, tailWord_5767986, baseEnd_5767986] using wordTrace_append hprefix tailTrace_5767986
  have hstable : (prefixWord ++ tailWord_5767986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5767986).length < 2 ^ (prefixWord ++ tailWord_5767986).sum := by decide
  have hdescent : baseEnd_5767986 < baseStart_5767986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5767986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768040 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5768040 : Nat := 118140960795 + 5768040 * 2 ^ 59
def prefixEnd_5768040 : Nat := 4983230072969 + 3 ^ 40 * 5768040 * 2
def baseEnd_5768040 : Nat := 2961776954359717750673273

theorem tailTrace_5768040 : CollatzResearch.WordTrace tailWord_5768040 prefixEnd_5768040 2961776954359717750673273 := by
  unfold tailWord_5768040
  simp only [CollatzResearch.WordTrace]
  refine ⟨105188851011691828824534787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140251801348922438432713049 105188851011691828824534787)
  ·
    refine ⟨157783276517537743236802181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105188851011691828824534787 157783276517537743236802181)
    ·
      refine ⟨29584364347038326856900409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157783276517537743236802181 29584364347038326856900409)
      ·
        refine ⟨22188273260278745142675307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29584364347038326856900409 22188273260278745142675307)
        ·
          refine ⟨33282409890418117714012961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22188273260278745142675307 33282409890418117714012961)
          ·
            refine ⟨24961807417813588285509721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33282409890418117714012961 24961807417813588285509721)
            ·
              refine ⟨18721355563360191214132291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24961807417813588285509721 18721355563360191214132291)
              ·
                refine ⟨28082033345040286821198437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18721355563360191214132291 28082033345040286821198437)
                ·
                  refine ⟨5265381252195053778974707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28082033345040286821198437 5265381252195053778974707)
                  ·
                    refine ⟨7898071878292580668462061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5265381252195053778974707 7898071878292580668462061)
                    ·
                      refine ⟨2961776954359717750673273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7898071878292580668462061 2961776954359717750673273)
                      ·
                        rfl

theorem cell23_5768040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5768040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768040 prefixEnd_5768040 := by exact prefixLift 5768040
  have htrace : WordTrace (prefixWord ++ tailWord_5768040) baseStart_5768040 baseEnd_5768040 := by
    simpa [prefixWord, tailWord_5768040, baseEnd_5768040] using wordTrace_append hprefix tailTrace_5768040
  have hstable : (prefixWord ++ tailWord_5768040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768040).length < 2 ^ (prefixWord ++ tailWord_5768040).sum := by decide
  have hdescent : baseEnd_5768040 < baseStart_5768040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768057 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 2, 1, 3]
def baseStart_5768057 : Nat := 118140960795 + 5768057 * 2 ^ 59
def prefixEnd_5768057 : Nat := 4983230072969 + 3 ^ 40 * 5768057 * 2
def baseEnd_5768057 : Nat := 2961785683530844184160695

theorem tailTrace_5768057 : CollatzResearch.WordTrace tailWord_5768057 prefixEnd_5768057 2961785683530844184160695 := by
  unfold tailWord_5768057
  simp only [CollatzResearch.WordTrace]
  refine ⟨210378322064322069552438425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140252214709548046368292283 210378322064322069552438425)
  ·
    refine ⟨157783741548241552164328819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210378322064322069552438425 157783741548241552164328819)
    ·
      refine ⟨236675612322362328246493229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157783741548241552164328819 236675612322362328246493229)
      ·
        refine ⟨88753354620885873092434961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236675612322362328246493229 88753354620885873092434961)
        ·
          refine ⟨66565015965664404819326221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88753354620885873092434961 66565015965664404819326221)
          ·
            refine ⟨24961880987124151807247333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66565015965664404819326221 24961880987124151807247333)
            ·
              refine ⟨4680352685085778463858875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24961880987124151807247333 4680352685085778463858875)
              ·
                refine ⟨7020529027628667695788313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680352685085778463858875 7020529027628667695788313)
                ·
                  refine ⟨5265396770721500771841235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7020529027628667695788313 5265396770721500771841235)
                  ·
                    refine ⟨7898095156082251157761853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5265396770721500771841235 7898095156082251157761853)
                    ·
                      refine ⟨2961785683530844184160695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7898095156082251157761853 2961785683530844184160695)
                      ·
                        rfl

theorem cell23_5768057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_5768057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768057 prefixEnd_5768057 := by exact prefixLift 5768057
  have htrace : WordTrace (prefixWord ++ tailWord_5768057) baseStart_5768057 baseEnd_5768057 := by
    simpa [prefixWord, tailWord_5768057, baseEnd_5768057] using wordTrace_append hprefix tailTrace_5768057
  have hstable : (prefixWord ++ tailWord_5768057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768057).length < 2 ^ (prefixWord ++ tailWord_5768057).sum := by decide
  have hdescent : baseEnd_5768057 < baseStart_5768057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768084 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_5768084 : Nat := 118140960795 + 5768084 * 2 ^ 59
def prefixEnd_5768084 : Nat := 4983230072969 + 3 ^ 40 * 5768084 * 2
def baseEnd_5768084 : Nat := 2961799547508515578523071

theorem tailTrace_5768084 : CollatzResearch.WordTrace tailWord_5768084 prefixEnd_5768084 2961799547508515578523071 := by
  unfold tailWord_5768084
  simp only [CollatzResearch.WordTrace]
  refine ⟨105189653417612126581835653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140252871223482835442447537 105189653417612126581835653)
  ·
    refine ⟨19723060015802273734094185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105189653417612126581835653 19723060015802273734094185)
    ·
      refine ⟨14792295011851705300570639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19723060015802273734094185 14792295011851705300570639)
      ·
        refine ⟨22188442517777557950855959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14792295011851705300570639 22188442517777557950855959)
        ·
          refine ⟨33282663776666336926283939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22188442517777557950855959 33282663776666336926283939)
          ·
            refine ⟨49923995664999505389425909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33282663776666336926283939 49923995664999505389425909)
            ·
              refine ⟨4680374593593703630258679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49923995664999505389425909 4680374593593703630258679)
              ·
                refine ⟨7020561890390555445388019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680374593593703630258679 7020561890390555445388019)
                ·
                  refine ⟨10530842835585833168082029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7020561890390555445388019 10530842835585833168082029)
                  ·
                    refine ⟨3949066063344687438030761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10530842835585833168082029 3949066063344687438030761)
                    ·
                      refine ⟨2961799547508515578523071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949066063344687438030761 2961799547508515578523071)
                      ·
                        rfl

theorem cell23_5768084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_5768084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768084 prefixEnd_5768084 := by exact prefixLift 5768084
  have htrace : WordTrace (prefixWord ++ tailWord_5768084) baseStart_5768084 baseEnd_5768084 := by
    simpa [prefixWord, tailWord_5768084, baseEnd_5768084] using wordTrace_append hprefix tailTrace_5768084
  have hstable : (prefixWord ++ tailWord_5768084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768084).length < 2 ^ (prefixWord ++ tailWord_5768084).sum := by decide
  have hdescent : baseEnd_5768084 < baseStart_5768084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768093 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_5768093 : Nat := 118140960795 + 5768093 * 2 ^ 59
def prefixEnd_5768093 : Nat := 4983230072969 + 3 ^ 40 * 5768093 * 2
def baseEnd_5768093 : Nat := 2961804168834406043310529

theorem tailTrace_5768093 : CollatzResearch.WordTrace tailWord_5768093 prefixEnd_5768093 2961804168834406043310529 := by
  unfold tailWord_5768093
  simp only [CollatzResearch.WordTrace]
  refine ⟨210379635092191647700748933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140253090061461098467165955 210379635092191647700748933)
  ·
    refine ⟨39446181579785933943890425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210379635092191647700748933 39446181579785933943890425)
    ·
      refine ⟨29584636184839450457917819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39446181579785933943890425 29584636184839450457917819)
      ·
        refine ⟨44376954277259175686876729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29584636184839450457917819 44376954277259175686876729)
        ·
          refine ⟨33282715707944381765157547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44376954277259175686876729 33282715707944381765157547)
          ·
            refine ⟨49924073561916572647736321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33282715707944381765157547 49924073561916572647736321)
            ·
              refine ⟨37443055171437429485802241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49924073561916572647736321 37443055171437429485802241)
              ·
                refine ⟨28082291378578072114351681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37443055171437429485802241 28082291378578072114351681)
                ·
                  refine ⟨21061718533933554085763761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28082291378578072114351681 21061718533933554085763761)
                  ·
                    refine ⟨15796288900450165564322821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21061718533933554085763761 15796288900450165564322821)
                    ·
                      refine ⟨2961804168834406043310529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15796288900450165564322821 2961804168834406043310529)
                      ·
                        rfl

theorem cell23_5768093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_5768093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768093 prefixEnd_5768093 := by exact prefixLift 5768093
  have htrace : WordTrace (prefixWord ++ tailWord_5768093) baseStart_5768093 baseEnd_5768093 := by
    simpa [prefixWord, tailWord_5768093, baseEnd_5768093] using wordTrace_append hprefix tailTrace_5768093
  have hstable : (prefixWord ++ tailWord_5768093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768093).length < 2 ^ (prefixWord ++ tailWord_5768093).sum := by decide
  have hdescent : baseEnd_5768093 < baseStart_5768093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768096 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_5768096 : Nat := 118140960795 + 5768096 * 2 ^ 59
def prefixEnd_5768096 : Nat := 4983230072969 + 3 ^ 40 * 5768096 * 2
def baseEnd_5768096 : Nat := 2961805709276369531573015

theorem tailTrace_5768096 : CollatzResearch.WordTrace tailWord_5768096 prefixEnd_5768096 2961805709276369531573015 := by
  unfold tailWord_5768096
  simp only [CollatzResearch.WordTrace]
  refine ⟨105189872255590389606554071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140253163007453852808738761 105189872255590389606554071)
  ·
    refine ⟨157784808383385584409831107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105189872255590389606554071 157784808383385584409831107)
    ·
      refine ⟨236677212575078376614746661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157784808383385584409831107 236677212575078376614746661)
      ·
        refine ⟨44376977357827195615264999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236677212575078376614746661 44376977357827195615264999)
        ·
          refine ⟨66565466036740793422897499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44376977357827195615264999 66565466036740793422897499)
          ·
            refine ⟨99848199055111190134346249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66565466036740793422897499 99848199055111190134346249)
            ·
              refine ⟨74886149291333392600759687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99848199055111190134346249 74886149291333392600759687)
              ·
                refine ⟨112329223937000088901139531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74886149291333392600759687 112329223937000088901139531)
                ·
                  refine ⟨168493835905500133351709297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112329223937000088901139531 168493835905500133351709297)
                  ·
                    refine ⟨126370376929125100013781973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168493835905500133351709297 126370376929125100013781973)
                    ·
                      refine ⟨2961805709276369531573015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126370376929125100013781973 2961805709276369531573015)
                      ·
                        rfl

theorem cell23_5768096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_5768096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768096 prefixEnd_5768096 := by exact prefixLift 5768096
  have htrace : WordTrace (prefixWord ++ tailWord_5768096) baseStart_5768096 baseEnd_5768096 := by
    simpa [prefixWord, tailWord_5768096, baseEnd_5768096] using wordTrace_append hprefix tailTrace_5768096
  have hstable : (prefixWord ++ tailWord_5768096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768096).length < 2 ^ (prefixWord ++ tailWord_5768096).sum := by decide
  have hdescent : baseEnd_5768096 < baseStart_5768096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768123 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 3, 7, 2]
def baseStart_5768123 : Nat := 118140960795 + 5768123 * 2 ^ 59
def prefixEnd_5768123 : Nat := 4983230072969 + 3 ^ 40 * 5768123 * 2
def baseEnd_5768123 : Nat := 2961819573254040925935391

theorem tailTrace_5768123 : CollatzResearch.WordTrace tailWord_5768123 prefixEnd_5768123 2961819573254040925935391 := by
  unfold tailWord_5768123
  simp only [CollatzResearch.WordTrace]
  refine ⟨210380729282082962824341023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140253819521388641882894015 210380729282082962824341023)
  ·
    refine ⟨315571093923124444236511535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210380729282082962824341023 315571093923124444236511535)
    ·
      refine ⟨473356640884686666354767303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315571093923124444236511535 473356640884686666354767303)
      ·
        refine ⟨710034961327029999532150955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473356640884686666354767303 710034961327029999532150955)
        ·
          refine ⟨1065052441990544999298226433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710034961327029999532150955 1065052441990544999298226433)
          ·
            refine ⟨798789331492908749473669825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065052441990544999298226433 798789331492908749473669825)
            ·
              refine ⟨599091998619681562105252369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798789331492908749473669825 599091998619681562105252369)
              ·
                refine ⟨449318998964761171578939277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599091998619681562105252369 449318998964761171578939277)
                ·
                  refine ⟨168494624611785439342102229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449318998964761171578939277 168494624611785439342102229)
                  ·
                    refine ⟨3949092764338721234580521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168494624611785439342102229 3949092764338721234580521)
                    ·
                      refine ⟨2961819573254040925935391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949092764338721234580521 2961819573254040925935391)
                      ·
                        rfl

theorem cell23_5768123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 7, 2].length) (baseStart_5768123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768123 prefixEnd_5768123 := by exact prefixLift 5768123
  have htrace : WordTrace (prefixWord ++ tailWord_5768123) baseStart_5768123 baseEnd_5768123 := by
    simpa [prefixWord, tailWord_5768123, baseEnd_5768123] using wordTrace_append hprefix tailTrace_5768123
  have hstable : (prefixWord ++ tailWord_5768123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768123).length < 2 ^ (prefixWord ++ tailWord_5768123).sum := by decide
  have hdescent : baseEnd_5768123 < baseStart_5768123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768193 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 8]
def baseStart_5768193 : Nat := 118140960795 + 5768193 * 2 ^ 59
def prefixEnd_5768193 : Nat := 4983230072969 + 3 ^ 40 * 5768193 * 2
def baseEnd_5768193 : Nat := 329095057433317294673341

theorem tailTrace_5768193 : CollatzResearch.WordTrace tailWord_5768193 prefixEnd_5768193 329095057433317294673341 := by
  unfold tailWord_5768193
  simp only [CollatzResearch.WordTrace]
  refine ⟨210383282391829364779389233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140255521594552909852926155 210383282391829364779389233)
  ·
    refine ⟨157787461793872023584541925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210383282391829364779389233 157787461793872023584541925)
    ·
      refine ⟨29585149086351004422101611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157787461793872023584541925 29585149086351004422101611)
      ·
        refine ⟨44377723629526506633152417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29585149086351004422101611 44377723629526506633152417)
        ·
          refine ⟨33283292722144879974864313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44377723629526506633152417 33283292722144879974864313)
          ·
            refine ⟨24962469541608659981148235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33283292722144879974864313 24962469541608659981148235)
            ·
              refine ⟨37443704312412989971722353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24962469541608659981148235 37443704312412989971722353)
              ·
                refine ⟨28082778234309742478791765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37443704312412989971722353 28082778234309742478791765)
                ·
                  refine ⟨329095057433317294673341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28082778234309742478791765 329095057433317294673341)
                  ·
                    rfl

theorem cell23_5768193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 8].length) (baseStart_5768193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768193 prefixEnd_5768193 := by exact prefixLift 5768193
  have htrace : WordTrace (prefixWord ++ tailWord_5768193) baseStart_5768193 baseEnd_5768193 := by
    simpa [prefixWord, tailWord_5768193, baseEnd_5768193] using wordTrace_append hprefix tailTrace_5768193
  have hstable : (prefixWord ++ tailWord_5768193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768193).length < 2 ^ (prefixWord ++ tailWord_5768193).sum := by decide
  have hdescent : baseEnd_5768193 < baseStart_5768193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768227 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 6]
def baseStart_5768227 : Nat := 118140960795 + 5768227 * 2 ^ 59
def prefixEnd_5768227 : Nat := 4983230072969 + 3 ^ 40 * 5768227 * 2
def baseEnd_5768227 : Nat := 329096997249123168781657

theorem tailTrace_5768227 : CollatzResearch.WordTrace tailWord_5768227 prefixEnd_5768227 329096997249123168781657 := by
  unfold tailWord_5768227
  simp only [CollatzResearch.WordTrace]
  refine ⟨210384522473706188586126935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140256348315804125724084623 210384522473706188586126935)
  ·
    refine ⟨315576783710559282879190403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210384522473706188586126935 315576783710559282879190403)
    ·
      refine ⟨473365175565838924318785605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315576783710559282879190403 473365175565838924318785605)
      ·
        refine ⟨88755970418594798309772301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 473365175565838924318785605 88755970418594798309772301)
        ·
          refine ⟨33283488906973049366164613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88755970418594798309772301 33283488906973049366164613)
          ·
            refine ⟨6240654170057446756155865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33283488906973049366164613 6240654170057446756155865)
            ·
              refine ⟨4680490627543085067116899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6240654170057446756155865 4680490627543085067116899)
              ·
                refine ⟨7020735941314627600675349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680490627543085067116899 7020735941314627600675349)
                ·
                  refine ⟨329096997249123168781657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7020735941314627600675349 329096997249123168781657)
                  ·
                    rfl

theorem cell23_5768227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 6].length) (baseStart_5768227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768227 prefixEnd_5768227 := by exact prefixLift 5768227
  have htrace : WordTrace (prefixWord ++ tailWord_5768227) baseStart_5768227 baseEnd_5768227 := by
    simpa [prefixWord, tailWord_5768227, baseEnd_5768227] using wordTrace_append hprefix tailTrace_5768227
  have hstable : (prefixWord ++ tailWord_5768227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768227).length < 2 ^ (prefixWord ++ tailWord_5768227).sum := by decide
  have hdescent : baseEnd_5768227 < baseStart_5768227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768273 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_5768273 : Nat := 118140960795 + 5768273 * 2 ^ 59
def prefixEnd_5768273 : Nat := 4983230072969 + 3 ^ 40 * 5768273 * 2
def baseEnd_5768273 : Nat := 2961896595352215339059701

theorem tailTrace_5768273 : CollatzResearch.WordTrace tailWord_5768273 prefixEnd_5768273 2961896595352215339059701 := by
  unfold tailWord_5768273
  simp only [CollatzResearch.WordTrace]
  refine ⟨210386200231539538442301473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140257466821026358961534315 210386200231539538442301473)
  ·
    refine ⟨157789650173654653831726105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210386200231539538442301473 157789650173654653831726105)
    ·
      refine ⟨118342237630240990373794579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157789650173654653831726105 118342237630240990373794579)
      ·
        refine ⟨177513356445361485560691869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118342237630240990373794579 177513356445361485560691869)
        ·
          refine ⟨66567508667010557085259451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177513356445361485560691869 66567508667010557085259451)
          ·
            refine ⟨99851263000515835627889177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66567508667010557085259451 99851263000515835627889177)
            ·
              refine ⟨74888447250386876720916883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99851263000515835627889177 74888447250386876720916883)
              ·
                refine ⟨112332670875580315081375325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74888447250386876720916883 112332670875580315081375325)
                ·
                  refine ⟨42124751578342618155515747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112332670875580315081375325 42124751578342618155515747)
                  ·
                    refine ⟨63187127367513927233273621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42124751578342618155515747 63187127367513927233273621)
                    ·
                      refine ⟨2961896595352215339059701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63187127367513927233273621 2961896595352215339059701)
                      ·
                        rfl

theorem cell23_5768273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_5768273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768273 prefixEnd_5768273 := by exact prefixLift 5768273
  have htrace : WordTrace (prefixWord ++ tailWord_5768273) baseStart_5768273 baseEnd_5768273 := by
    simpa [prefixWord, tailWord_5768273, baseEnd_5768273] using wordTrace_append hprefix tailTrace_5768273
  have hstable : (prefixWord ++ tailWord_5768273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768273).length < 2 ^ (prefixWord ++ tailWord_5768273).sum := by decide
  have hdescent : baseEnd_5768273 < baseStart_5768273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768280 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_5768280 : Nat := 118140960795 + 5768280 * 2 ^ 59
def prefixEnd_5768280 : Nat := 4983230072969 + 3 ^ 40 * 5768280 * 2
def baseEnd_5768280 : Nat := 2961900189716796811672169

theorem tailTrace_5768280 : CollatzResearch.WordTrace tailWord_5768280 prefixEnd_5768280 2961900189716796811672169 := by
  unfold tailWord_5768280
  simp only [CollatzResearch.WordTrace]
  refine ⟨105193227771257089318903147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140257637028342785758537529 105193227771257089318903147)
  ·
    refine ⟨157789841656885633978354721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105193227771257089318903147 157789841656885633978354721)
    ·
      refine ⟨118342381242664225483766041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157789841656885633978354721 118342381242664225483766041)
      ·
        refine ⟨88756785931998169112824531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118342381242664225483766041 88756785931998169112824531)
        ·
          refine ⟨133135178897997253669236797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88756785931998169112824531 133135178897997253669236797)
          ·
            refine ⟨49925692086748970125963799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133135178897997253669236797 49925692086748970125963799)
            ·
              refine ⟨74888538130123455188945699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49925692086748970125963799 74888538130123455188945699)
              ·
                refine ⟨112332807195185182783418549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74888538130123455188945699 112332807195185182783418549)
                ·
                  refine ⟨10531200674548610885945489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112332807195185182783418549 10531200674548610885945489)
                  ·
                    refine ⟨7898400505911458164459117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10531200674548610885945489 7898400505911458164459117)
                    ·
                      refine ⟨2961900189716796811672169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7898400505911458164459117 2961900189716796811672169)
                      ·
                        rfl

theorem cell23_5768280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_5768280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768280 prefixEnd_5768280 := by exact prefixLift 5768280
  have htrace : WordTrace (prefixWord ++ tailWord_5768280) baseStart_5768280 baseEnd_5768280 := by
    simpa [prefixWord, tailWord_5768280, baseEnd_5768280] using wordTrace_append hprefix tailTrace_5768280
  have hstable : (prefixWord ++ tailWord_5768280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768280).length < 2 ^ (prefixWord ++ tailWord_5768280).sum := by decide
  have hdescent : baseEnd_5768280 < baseStart_5768280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768300 : List Nat := [2, 2, 1, 1, 3, 2, 5, 7]
def baseStart_5768300 : Nat := 118140960795 + 5768300 * 2 ^ 59
def prefixEnd_5768300 : Nat := 4983230072969 + 3 ^ 40 * 5768300 * 2
def baseEnd_5768300 : Nat := 109700387382588397534151

theorem tailTrace_5768300 : CollatzResearch.WordTrace tailWord_5768300 prefixEnd_5768300 109700387382588397534151 := by
  unfold tailWord_5768300
  simp only [CollatzResearch.WordTrace]
  refine ⟨105193592501220861026767177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140258123334961148035689569 105193592501220861026767177)
  ·
    refine ⟨78895194375915645770075383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105193592501220861026767177 78895194375915645770075383)
    ·
      refine ⟨118342791563873468655113075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78895194375915645770075383 118342791563873468655113075)
      ·
        refine ⟨177514187345810202982669613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118342791563873468655113075 177514187345810202982669613)
        ·
          refine ⟨66567820254678826118501105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177514187345810202982669613 66567820254678826118501105)
          ·
            refine ⟨49925865191009119588875829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66567820254678826118501105 49925865191009119588875829)
            ·
              refine ⟨4680549861657104961457109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49925865191009119588875829 4680549861657104961457109)
              ·
                refine ⟨109700387382588397534151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4680549861657104961457109 109700387382588397534151)
                ·
                  rfl

theorem cell23_5768300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 7].length) (baseStart_5768300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768300 prefixEnd_5768300 := by exact prefixLift 5768300
  have htrace : WordTrace (prefixWord ++ tailWord_5768300) baseStart_5768300 baseEnd_5768300 := by
    simpa [prefixWord, tailWord_5768300, baseEnd_5768300] using wordTrace_append hprefix tailTrace_5768300
  have hstable : (prefixWord ++ tailWord_5768300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768300).length < 2 ^ (prefixWord ++ tailWord_5768300).sum := by decide
  have hdescent : baseEnd_5768300 < baseStart_5768300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768311 : List Nat := [1, 1, 3, 1, 1, 4, 4, 3, 1, 2, 2]
def baseStart_5768311 : Nat := 118140960795 + 5768311 * 2 ^ 59
def prefixEnd_5768311 : Nat := 4983230072969 + 3 ^ 40 * 5768311 * 2
def baseEnd_5768311 : Nat := 2961916107617086190384527

theorem tailTrace_5768311 : CollatzResearch.WordTrace tailWord_5768311 prefixEnd_5768311 2961916107617086190384527 := by
  unfold tailWord_5768311
  simp only [CollatzResearch.WordTrace]
  refine ⟨210387586205401870932184787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140258390803601247288123191 210387586205401870932184787)
  ·
    refine ⟨315581379308102806398277181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210387586205401870932184787 315581379308102806398277181)
    ·
      refine ⟨118343017240538552399353943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315581379308102806398277181 118343017240538552399353943)
      ·
        refine ⟨177514525860807828599030915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118343017240538552399353943 177514525860807828599030915)
        ·
          refine ⟨266271788791211742898546373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177514525860807828599030915 266271788791211742898546373)
          ·
            refine ⟨49925960398352201793477445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266271788791211742898546373 49925960398352201793477445)
            ·
              refine ⟨9361117574691037836277021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49925960398352201793477445 9361117574691037836277021)
              ·
                refine ⟨3510419090509139188603883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9361117574691037836277021 3510419090509139188603883)
                ·
                  refine ⟨5265628635763708782905825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510419090509139188603883 5265628635763708782905825)
                  ·
                    refine ⟨3949221476822781587179369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5265628635763708782905825 3949221476822781587179369)
                    ·
                      refine ⟨2961916107617086190384527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949221476822781587179369 2961916107617086190384527)
                      ·
                        rfl

theorem cell23_5768311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_5768311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768311 prefixEnd_5768311 := by exact prefixLift 5768311
  have htrace : WordTrace (prefixWord ++ tailWord_5768311) baseStart_5768311 baseEnd_5768311 := by
    simpa [prefixWord, tailWord_5768311, baseEnd_5768311] using wordTrace_append hprefix tailTrace_5768311
  have hstable : (prefixWord ++ tailWord_5768311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768311).length < 2 ^ (prefixWord ++ tailWord_5768311).sum := by decide
  have hdescent : baseEnd_5768311 < baseStart_5768311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768344 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_5768344 : Nat := 118140960795 + 5768344 * 2 ^ 59
def prefixEnd_5768344 : Nat := 4983230072969 + 3 ^ 40 * 5768344 * 2
def baseEnd_5768344 : Nat := 2961933052478684561271875

theorem tailTrace_5768344 : CollatzResearch.WordTrace tailWord_5768344 prefixEnd_5768344 2961933052478684561271875 := by
  unfold tailWord_5768344
  simp only [CollatzResearch.WordTrace]
  refine ⟨105194394907141158784068043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140259193209521545045424057 105194394907141158784068043)
  ·
    refine ⟨157791592360711738176102065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105194394907141158784068043 157791592360711738176102065)
    ·
      refine ⟨118343694270533803632076549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157791592360711738176102065 118343694270533803632076549)
      ·
        refine ⟨22189442675725088181014353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118343694270533803632076549 22189442675725088181014353)
        ·
          refine ⟨16642082006793816135760765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22189442675725088181014353 16642082006793816135760765)
          ·
            refine ⟨6240780752547681050910287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16642082006793816135760765 6240780752547681050910287)
            ·
              refine ⟨9361171128821521576365431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6240780752547681050910287 9361171128821521576365431)
              ·
                refine ⟨14041756693232282364548147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9361171128821521576365431 14041756693232282364548147)
                ·
                  refine ⟨21062635039848423546822221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14041756693232282364548147 21062635039848423546822221)
                  ·
                    refine ⟨7898488139943158830058333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21062635039848423546822221 7898488139943158830058333)
                    ·
                      refine ⟨2961933052478684561271875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7898488139943158830058333 2961933052478684561271875)
                      ·
                        rfl

theorem cell23_5768344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_5768344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768344 prefixEnd_5768344 := by exact prefixLift 5768344
  have htrace : WordTrace (prefixWord ++ tailWord_5768344) baseStart_5768344 baseEnd_5768344 := by
    simpa [prefixWord, tailWord_5768344, baseEnd_5768344] using wordTrace_append hprefix tailTrace_5768344
  have hstable : (prefixWord ++ tailWord_5768344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768344).length < 2 ^ (prefixWord ++ tailWord_5768344).sum := by decide
  have hdescent : baseEnd_5768344 < baseStart_5768344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768367 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 1, 4, 2]
def baseStart_5768367 : Nat := 118140960795 + 5768367 * 2 ^ 59
def prefixEnd_5768367 : Nat := 4983230072969 + 3 ^ 40 * 5768367 * 2
def baseEnd_5768367 : Nat := 2961944862533737971284269

theorem tailTrace_5768367 : CollatzResearch.WordTrace tailWord_5768367 prefixEnd_5768367 2961944862533737971284269 := by
  unfold tailWord_5768367
  simp only [CollatzResearch.WordTrace]
  refine ⟨210389628693198992496223355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140259752462132661664148903 210389628693198992496223355)
  ·
    refine ⟨315584443039798488744335033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210389628693198992496223355 315584443039798488744335033)
    ·
      refine ⟨236688332279848866558251275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315584443039798488744335033 236688332279848866558251275)
      ·
        refine ⟨355032498419773299837376913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236688332279848866558251275 355032498419773299837376913)
        ·
          refine ⟨266274373814829974878032685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355032498419773299837376913 266274373814829974878032685)
          ·
            refine ⟨99852890180561240579262257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266274373814829974878032685 99852890180561240579262257)
            ·
              refine ⟨74889667635420930434446693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99852890180561240579262257 74889667635420930434446693)
              ·
                refine ⟨14041812681641424456458755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74889667635420930434446693 14041812681641424456458755)
                ·
                  refine ⟨21062719022462136684688133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14041812681641424456458755 21062719022462136684688133)
                  ·
                    refine ⟨3949259816711650628379025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21062719022462136684688133 3949259816711650628379025)
                    ·
                      refine ⟨2961944862533737971284269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949259816711650628379025 2961944862533737971284269)
                      ·
                        rfl

theorem cell23_5768367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 4, 2].length) (baseStart_5768367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768367 prefixEnd_5768367 := by exact prefixLift 5768367
  have htrace : WordTrace (prefixWord ++ tailWord_5768367) baseStart_5768367 baseEnd_5768367 := by
    simpa [prefixWord, tailWord_5768367, baseEnd_5768367] using wordTrace_append hprefix tailTrace_5768367
  have hstable : (prefixWord ++ tailWord_5768367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768367).length < 2 ^ (prefixWord ++ tailWord_5768367).sum := by decide
  have hdescent : baseEnd_5768367 < baseStart_5768367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768370 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_5768370 : Nat := 118140960795 + 5768370 * 2 ^ 59
def prefixEnd_5768370 : Nat := 4983230072969 + 3 ^ 40 * 5768370 * 2
def baseEnd_5768370 : Nat := 2961946402975701459546755

theorem tailTrace_5768370 : CollatzResearch.WordTrace tailWord_5768370 prefixEnd_5768370 2961946402975701459546755 := by
  unfold tailWord_5768370
  simp only [CollatzResearch.WordTrace]
  refine ⟨52597434528047031002145641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140259825408125416005721709 52597434528047031002145641)
  ·
    refine ⟨39448075896035273251609231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52597434528047031002145641 39448075896035273251609231)
    ·
      refine ⟨59172113844052909877413847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39448075896035273251609231 59172113844052909877413847)
      ·
        refine ⟨88758170766079364816120771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59172113844052909877413847 88758170766079364816120771)
        ·
          refine ⟨133137256149119047224181157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88758170766079364816120771 133137256149119047224181157)
          ·
            refine ⟨24963235527959821354533967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133137256149119047224181157 24963235527959821354533967)
            ·
              refine ⟨37444853291939732031800951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24963235527959821354533967 37444853291939732031800951)
              ·
                refine ⟨56167279937909598047701427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37444853291939732031800951 56167279937909598047701427)
                ·
                  refine ⟨84250919906864397071552141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56167279937909598047701427 84250919906864397071552141)
                  ·
                    refine ⟨31594094965074148901832053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84250919906864397071552141 31594094965074148901832053)
                    ·
                      refine ⟨2961946402975701459546755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31594094965074148901832053 2961946402975701459546755)
                      ·
                        rfl

theorem cell23_5768370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_5768370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768370 prefixEnd_5768370 := by exact prefixLift 5768370
  have htrace : WordTrace (prefixWord ++ tailWord_5768370) baseStart_5768370 baseEnd_5768370 := by
    simpa [prefixWord, tailWord_5768370, baseEnd_5768370] using wordTrace_append hprefix tailTrace_5768370
  have hstable : (prefixWord ++ tailWord_5768370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768370).length < 2 ^ (prefixWord ++ tailWord_5768370).sum := by decide
  have hdescent : baseEnd_5768370 < baseStart_5768370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768420 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_5768420 : Nat := 118140960795 + 5768420 * 2 ^ 59
def prefixEnd_5768420 : Nat := 4983230072969 + 3 ^ 40 * 5768420 * 2
def baseEnd_5768420 : Nat := 987324025669475421307175

theorem tailTrace_5768420 : CollatzResearch.WordTrace tailWord_5768420 prefixEnd_5768420 987324025669475421307175 := by
  unfold tailWord_5768420
  simp only [CollatzResearch.WordTrace]
  refine ⟨105195780881003491273951357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140261041174671321698601809 105195780881003491273951357)
  ·
    refine ⟨39448417830376309227731759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105195780881003491273951357 39448417830376309227731759)
    ·
      refine ⟨59172626745564463841597639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39448417830376309227731759 59172626745564463841597639)
      ·
        refine ⟨88758940118346695762396459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59172626745564463841597639 88758940118346695762396459)
        ·
          refine ⟨133138410177520043643594689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88758940118346695762396459 133138410177520043643594689)
          ·
            refine ⟨99853807633140032732696017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133138410177520043643594689 99853807633140032732696017)
            ·
              refine ⟨74890355724855024549522013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99853807633140032732696017 74890355724855024549522013)
              ·
                refine ⟨28083883396820634206070755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74890355724855024549522013 28083883396820634206070755)
                ·
                  refine ⟨42125825095230951309106133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28083883396820634206070755 42125825095230951309106133)
                  ·
                    refine ⟨987324025669475421307175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42125825095230951309106133 987324025669475421307175)
                    ·
                      rfl

theorem cell23_5768420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_5768420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768420 prefixEnd_5768420 := by exact prefixLift 5768420
  have htrace : WordTrace (prefixWord ++ tailWord_5768420) baseStart_5768420 baseEnd_5768420 := by
    simpa [prefixWord, tailWord_5768420, baseEnd_5768420] using wordTrace_append hprefix tailTrace_5768420
  have hstable : (prefixWord ++ tailWord_5768420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768420).length < 2 ^ (prefixWord ++ tailWord_5768420).sum := by decide
  have hdescent : baseEnd_5768420 < baseStart_5768420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768440 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_5768440 : Nat := 118140960795 + 5768440 * 2 ^ 59
def prefixEnd_5768440 : Nat := 4983230072969 + 3 ^ 40 * 5768440 * 2
def baseEnd_5768440 : Nat := 2961982346621516185671433

theorem tailTrace_5768440 : CollatzResearch.WordTrace tailWord_5768440 prefixEnd_5768440 2961982346621516185671433 := by
  unfold tailWord_5768440
  simp only [CollatzResearch.WordTrace]
  refine ⟨105196145610967262981815387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140261527481289683975753849 105196145610967262981815387)
  ·
    refine ⟨157794218416450894472723081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105196145610967262981815387 157794218416450894472723081)
    ·
      refine ⟨118345663812338170854542311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157794218416450894472723081 118345663812338170854542311)
      ·
        refine ⟨177518495718507256281813467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118345663812338170854542311 177518495718507256281813467)
        ·
          refine ⟨266277743577760884422720201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177518495718507256281813467 266277743577760884422720201)
          ·
            refine ⟨199708307683320663317040151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266277743577760884422720201 199708307683320663317040151)
            ·
              refine ⟨299562461524980994975560227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199708307683320663317040151 299562461524980994975560227)
              ·
                refine ⟨449343692287471492463340341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299562461524980994975560227 449343692287471492463340341)
                ·
                  refine ⟨42125971151950452418438157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 449343692287471492463340341 42125971151950452418438157)
                  ·
                    refine ⟨15797239181981419656914309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42125971151950452418438157 15797239181981419656914309)
                    ·
                      refine ⟨2961982346621516185671433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15797239181981419656914309 2961982346621516185671433)
                      ·
                        rfl

theorem cell23_5768440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_5768440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768440 prefixEnd_5768440 := by exact prefixLift 5768440
  have htrace : WordTrace (prefixWord ++ tailWord_5768440) baseStart_5768440 baseEnd_5768440 := by
    simpa [prefixWord, tailWord_5768440, baseEnd_5768440] using wordTrace_append hprefix tailTrace_5768440
  have hstable : (prefixWord ++ tailWord_5768440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768440).length < 2 ^ (prefixWord ++ tailWord_5768440).sum := by decide
  have hdescent : baseEnd_5768440 < baseStart_5768440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768474 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_5768474 : Nat := 118140960795 + 5768474 * 2 ^ 59
def prefixEnd_5768474 : Nat := 4983230072969 + 3 ^ 40 * 5768474 * 2
def baseEnd_5768474 : Nat := 2961999804963769052646277

theorem tailTrace_5768474 : CollatzResearch.WordTrace tailWord_5768474 prefixEnd_5768474 2961999804963769052646277 := by
  unfold tailWord_5768474
  simp only [CollatzResearch.WordTrace]
  refine ⟨52598382825952837442592119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140262354202540899846912317 52598382825952837442592119)
  ·
    refine ⟨78897574238929256163888179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52598382825952837442592119 78897574238929256163888179)
    ·
      refine ⟨118346361358393884245832269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78897574238929256163888179 118346361358393884245832269)
      ·
        refine ⟨44379885509397706592187101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118346361358393884245832269 44379885509397706592187101)
        ·
          refine ⟨16642457066024139972070163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44379885509397706592187101 16642457066024139972070163)
          ·
            refine ⟨24963685599036209958105245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16642457066024139972070163 24963685599036209958105245)
            ·
              refine ⟨9361382099638578734289467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24963685599036209958105245 9361382099638578734289467)
              ·
                refine ⟨14042073149457868101434201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9361382099638578734289467 14042073149457868101434201)
                ·
                  refine ⟨10531554862093401076075651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14042073149457868101434201 10531554862093401076075651)
                  ·
                    refine ⟨15797332293140101614113477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10531554862093401076075651 15797332293140101614113477)
                    ·
                      refine ⟨2961999804963769052646277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15797332293140101614113477 2961999804963769052646277)
                      ·
                        rfl

theorem cell23_5768474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_5768474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768474 prefixEnd_5768474 := by exact prefixLift 5768474
  have htrace : WordTrace (prefixWord ++ tailWord_5768474) baseStart_5768474 baseEnd_5768474 := by
    simpa [prefixWord, tailWord_5768474, baseEnd_5768474] using wordTrace_append hprefix tailTrace_5768474
  have hstable : (prefixWord ++ tailWord_5768474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768474).length < 2 ^ (prefixWord ++ tailWord_5768474).sum := by decide
  have hdescent : baseEnd_5768474 < baseStart_5768474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768497 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 8]
def baseStart_5768497 : Nat := 118140960795 + 5768497 * 2 ^ 59
def prefixEnd_5768497 : Nat := 4983230072969 + 3 ^ 40 * 5768497 * 2
def baseEnd_5768497 : Nat := 329112401668758051406519

theorem tailTrace_5768497 : CollatzResearch.WordTrace tailWord_5768497 prefixEnd_5768497 329112401668758051406519 := by
  unfold tailWord_5768497
  simp only [CollatzResearch.WordTrace]
  refine ⟨210394370182728024698455745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140262913455152016465637163 210394370182728024698455745)
  ·
    refine ⟨157795777637046018523841809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210394370182728024698455745 157795777637046018523841809)
    ·
      refine ⟨118346833227784513892881357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157795777637046018523841809 118346833227784513892881357)
      ·
        refine ⟨44380062460419192709830509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118346833227784513892881357 44380062460419192709830509)
        ·
          refine ⟨16642523422657197266186441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44380062460419192709830509 16642523422657197266186441)
          ·
            refine ⟨12481892566992897949639831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16642523422657197266186441 12481892566992897949639831)
            ·
              refine ⟨18722838850489346924459747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12481892566992897949639831 18722838850489346924459747)
              ·
                refine ⟨28084258275734020386689621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18722838850489346924459747 28084258275734020386689621)
                ·
                  refine ⟨329112401668758051406519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28084258275734020386689621 329112401668758051406519)
                  ·
                    rfl

theorem cell23_5768497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 8].length) (baseStart_5768497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768497 prefixEnd_5768497 := by exact prefixLift 5768497
  have htrace : WordTrace (prefixWord ++ tailWord_5768497) baseStart_5768497 baseEnd_5768497 := by
    simpa [prefixWord, tailWord_5768497, baseEnd_5768497] using wordTrace_append hprefix tailTrace_5768497
  have hstable : (prefixWord ++ tailWord_5768497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768497).length < 2 ^ (prefixWord ++ tailWord_5768497).sum := by decide
  have hdescent : baseEnd_5768497 < baseStart_5768497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768501 : List Nat := [1, 3, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_5768501 : Nat := 118140960795 + 5768501 * 2 ^ 59
def prefixEnd_5768501 : Nat := 4983230072969 + 3 ^ 40 * 5768501 * 2
def baseEnd_5768501 : Nat := 987337889647146815669551

theorem tailTrace_5768501 : CollatzResearch.WordTrace tailWord_5768501 prefixEnd_5768501 987337889647146815669551 := by
  unfold tailWord_5768501
  simp only [CollatzResearch.WordTrace]
  refine ⟨210394516074713533381601357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140263010716475688921067571 210394516074713533381601357)
  ·
    refine ⟨78897943528017575018100509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210394516074713533381601357 78897943528017575018100509)
    ·
      refine ⟨29586728823006590631787691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78897943528017575018100509 29586728823006590631787691)
      ·
        refine ⟨44380093234509885947681537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29586728823006590631787691 44380093234509885947681537)
        ·
          refine ⟨33285069925882414460761153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44380093234509885947681537 33285069925882414460761153)
          ·
            refine ⟨24963802444411810845570865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33285069925882414460761153 24963802444411810845570865)
            ·
              refine ⟨18722851833308858134178149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24963802444411810845570865 18722851833308858134178149)
              ·
                refine ⟨3510534718745410900158403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18722851833308858134178149 3510534718745410900158403)
                ·
                  refine ⟨5265802078118116350237605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510534718745410900158403 5265802078118116350237605)
                  ·
                    refine ⟨987337889647146815669551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5265802078118116350237605 987337889647146815669551)
                    ·
                      rfl

theorem cell23_5768501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_5768501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768501 prefixEnd_5768501 := by exact prefixLift 5768501
  have htrace : WordTrace (prefixWord ++ tailWord_5768501) baseStart_5768501 baseEnd_5768501 := by
    simpa [prefixWord, tailWord_5768501, baseEnd_5768501] using wordTrace_append hprefix tailTrace_5768501
  have hstable : (prefixWord ++ tailWord_5768501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768501).length < 2 ^ (prefixWord ++ tailWord_5768501).sum := by decide
  have hdescent : baseEnd_5768501 < baseStart_5768501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768544 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 1, 5]
def baseStart_5768544 : Nat := 118140960795 + 5768544 * 2 ^ 59
def prefixEnd_5768544 : Nat := 4983230072969 + 3 ^ 40 * 5768544 * 2
def baseEnd_5768544 : Nat := 987345249536527926256985

theorem tailTrace_5768544 : CollatzResearch.WordTrace tailWord_5768544 prefixEnd_5768544 987345249536527926256985 := by
  unfold tailWord_5768544
  simp only [CollatzResearch.WordTrace]
  refine ⟨105198042206778875862708343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140264056275705167816944457 105198042206778875862708343)
  ·
    refine ⟨157797063310168313794062515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105198042206778875862708343 157797063310168313794062515)
    ·
      refine ⟨236695594965252470691093773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157797063310168313794062515 236695594965252470691093773)
      ·
        refine ⟨88760848111969676509160165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236695594965252470691093773 88760848111969676509160165)
        ·
          refine ⟨16642659020994314345467531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88760848111969676509160165 16642659020994314345467531)
          ·
            refine ⟨24963988531491471518201297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16642659020994314345467531 24963988531491471518201297)
            ·
              refine ⟨18722991398618603638650973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24963988531491471518201297 18722991398618603638650973)
              ·
                refine ⟨7021121774481976364494115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18722991398618603638650973 7021121774481976364494115)
                ·
                  refine ⟨10531682661722964546741173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021121774481976364494115 10531682661722964546741173)
                  ·
                    refine ⟨987345249536527926256985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10531682661722964546741173 987345249536527926256985)
                    ·
                      rfl

theorem cell23_5768544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_5768544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768544 prefixEnd_5768544 := by exact prefixLift 5768544
  have htrace : WordTrace (prefixWord ++ tailWord_5768544) baseStart_5768544 baseEnd_5768544 := by
    simpa [prefixWord, tailWord_5768544, baseEnd_5768544] using wordTrace_append hprefix tailTrace_5768544
  have hstable : (prefixWord ++ tailWord_5768544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768544).length < 2 ^ (prefixWord ++ tailWord_5768544).sum := by decide
  have hdescent : baseEnd_5768544 < baseStart_5768544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768567 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_5768567 : Nat := 118140960795 + 5768567 * 2 ^ 59
def prefixEnd_5768567 : Nat := 4983230072969 + 3 ^ 40 * 5768567 * 2
def baseEnd_5768567 : Nat := 2962047558664637188783349

theorem tailTrace_5768567 : CollatzResearch.WordTrace tailWord_5768567 prefixEnd_5768567 2962047558664637188783349 := by
  unfold tailWord_5768567
  simp only [CollatzResearch.WordTrace]
  refine ⟨210396923292474426653503955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140264615528316284435669303 210396923292474426653503955)
  ·
    refine ⟨315595384938711639980255933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210396923292474426653503955 315595384938711639980255933)
    ·
      refine ⟨118348269352016864992595975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315595384938711639980255933 118348269352016864992595975)
      ·
        refine ⟨177522404028025297488893963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118348269352016864992595975 177522404028025297488893963)
        ·
          refine ⟨266283606042037946233340945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177522404028025297488893963 266283606042037946233340945)
          ·
            refine ⟨199712704531528459675005709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266283606042037946233340945 199712704531528459675005709)
            ·
              refine ⟨74892264199323172378127141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199712704531528459675005709 74892264199323172378127141)
              ·
                refine ⟨14042299537373094820898839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74892264199323172378127141 14042299537373094820898839)
                ·
                  refine ⟨21063449306059642231348259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14042299537373094820898839 21063449306059642231348259)
                  ·
                    refine ⟨31595173959089463347022389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21063449306059642231348259 31595173959089463347022389)
                    ·
                      refine ⟨2962047558664637188783349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31595173959089463347022389 2962047558664637188783349)
                      ·
                        rfl

theorem cell23_5768567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_5768567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768567 prefixEnd_5768567 := by exact prefixLift 5768567
  have htrace : WordTrace (prefixWord ++ tailWord_5768567) baseStart_5768567 baseEnd_5768567 := by
    simpa [prefixWord, tailWord_5768567, baseEnd_5768567] using wordTrace_append hprefix tailTrace_5768567
  have hstable : (prefixWord ++ tailWord_5768567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768567).length < 2 ^ (prefixWord ++ tailWord_5768567).sum := by decide
  have hdescent : baseEnd_5768567 < baseStart_5768567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768578 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5768578 : Nat := 118140960795 + 5768578 * 2 ^ 59
def prefixEnd_5768578 : Nat := 4983230072969 + 3 ^ 40 * 5768578 * 2
def baseEnd_5768578 : Nat := 987351068983945548581933

theorem tailTrace_5768578 : CollatzResearch.WordTrace tailWord_5768578 prefixEnd_5768578 987351068983945548581933 := by
  unfold tailWord_5768578
  simp only [CollatzResearch.WordTrace]
  refine ⟨52599331123858643883038597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140264882996956383688102925 52599331123858643883038597)
  ·
    refine ⟨9862374585723495728069737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52599331123858643883038597 9862374585723495728069737)
    ·
      refine ⟨7396780939292621796052303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9862374585723495728069737 7396780939292621796052303)
      ·
        refine ⟨11095171408938932694078455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396780939292621796052303 11095171408938932694078455)
        ·
          refine ⟨16642757113408399041117683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11095171408938932694078455 16642757113408399041117683)
          ·
            refine ⟨24964135670112598561676525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16642757113408399041117683 24964135670112598561676525)
            ·
              refine ⟨9361550876292224460628697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24964135670112598561676525 9361550876292224460628697)
              ·
                refine ⟨7021163157219168345471523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9361550876292224460628697 7021163157219168345471523)
                ·
                  refine ⟨10531744735828752518207285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021163157219168345471523 10531744735828752518207285)
                  ·
                    refine ⟨987351068983945548581933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10531744735828752518207285 987351068983945548581933)
                    ·
                      rfl

theorem cell23_5768578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5768578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768578 prefixEnd_5768578 := by exact prefixLift 5768578
  have htrace : WordTrace (prefixWord ++ tailWord_5768578) baseStart_5768578 baseEnd_5768578 := by
    simpa [prefixWord, tailWord_5768578, baseEnd_5768578] using wordTrace_append hprefix tailTrace_5768578
  have hstable : (prefixWord ++ tailWord_5768578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768578).length < 2 ^ (prefixWord ++ tailWord_5768578).sum := by decide
  have hdescent : baseEnd_5768578 < baseStart_5768578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768581 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 3, 2, 2]
def baseStart_5768581 : Nat := 118140960795 + 5768581 * 2 ^ 59
def prefixEnd_5768581 : Nat := 4983230072969 + 3 ^ 40 * 5768581 * 2
def baseEnd_5768581 : Nat := 2962054747393800134008285

theorem tailTrace_5768581 : CollatzResearch.WordTrace tailWord_5768581 prefixEnd_5768581 2962054747393800134008285 := by
  unfold tailWord_5768581
  simp only [CollatzResearch.WordTrace]
  refine ⟨210397433914423707044513597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140264955942949138029675731 210397433914423707044513597)
  ·
    refine ⟨78899037717908890141692599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210397433914423707044513597 78899037717908890141692599)
    ·
      refine ⟨118348556576863335212538899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78899037717908890141692599 118348556576863335212538899)
      ·
        refine ⟨177522834865295002818808349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118348556576863335212538899 177522834865295002818808349)
        ·
          refine ⟨66571063074485626057053131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177522834865295002818808349 66571063074485626057053131)
          ·
            refine ⟨99856594611728439085579697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66571063074485626057053131 99856594611728439085579697)
            ·
              refine ⟨74892445958796329314184773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99856594611728439085579697 74892445958796329314184773)
              ·
                refine ⟨14042333617274311746409645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74892445958796329314184773 14042333617274311746409645)
                ·
                  refine ⟨5265875106477866904903617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14042333617274311746409645 5265875106477866904903617)
                  ·
                    refine ⟨3949406329858400178677713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5265875106477866904903617 3949406329858400178677713)
                    ·
                      refine ⟨2962054747393800134008285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949406329858400178677713 2962054747393800134008285)
                      ·
                        rfl

theorem cell23_5768581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_5768581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768581 prefixEnd_5768581 := by exact prefixLift 5768581
  have htrace : WordTrace (prefixWord ++ tailWord_5768581) baseStart_5768581 baseEnd_5768581 := by
    simpa [prefixWord, tailWord_5768581, baseEnd_5768581] using wordTrace_append hprefix tailTrace_5768581
  have hstable : (prefixWord ++ tailWord_5768581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768581).length < 2 ^ (prefixWord ++ tailWord_5768581).sum := by decide
  have hdescent : baseEnd_5768581 < baseStart_5768581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768604 : List Nat := [2, 2, 3, 4, 1, 11]
def baseStart_5768604 : Nat := 118140960795 + 5768604 * 2 ^ 59
def prefixEnd_5768604 : Nat := 4983230072969 + 3 ^ 40 * 5768604 * 2
def baseEnd_5768604 : Nat := 12189574310489109234653

theorem tailTrace_5768604 : CollatzResearch.WordTrace tailWord_5768604 prefixEnd_5768604 12189574310489109234653 := by
  unfold tailWord_5768604
  simp only [CollatzResearch.WordTrace]
  refine ⟨105199136396670190986300433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140265515195560254648400577 105199136396670190986300433)
  ·
    refine ⟨78899352297502643239725325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105199136396670190986300433 78899352297502643239725325)
    ·
      refine ⟨29587257111563491214896997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78899352297502643239725325 29587257111563491214896997)
      ·
        refine ⟨5547610708418154602793187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29587257111563491214896997 5547610708418154602793187)
        ·
          refine ⟨8321416062627231904189781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5547610708418154602793187 8321416062627231904189781)
          ·
            refine ⟨12189574310489109234653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8321416062627231904189781 12189574310489109234653)
            ·
              rfl

theorem cell23_5768604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 11].length) (baseStart_5768604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768604 prefixEnd_5768604 := by exact prefixLift 5768604
  have htrace : WordTrace (prefixWord ++ tailWord_5768604) baseStart_5768604 baseEnd_5768604 := by
    simpa [prefixWord, tailWord_5768604, baseEnd_5768604] using wordTrace_append hprefix tailTrace_5768604
  have hstable : (prefixWord ++ tailWord_5768604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768604).length < 2 ^ (prefixWord ++ tailWord_5768604).sum := by decide
  have hdescent : baseEnd_5768604 < baseStart_5768604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768615 : List Nat := [1, 1, 6, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_5768615 : Nat := 118140960795 + 5768615 * 2 ^ 59
def prefixEnd_5768615 : Nat := 4983230072969 + 3 ^ 40 * 5768615 * 2
def baseEnd_5768615 : Nat := 2962072205736053000983129

theorem tailTrace_5768615 : CollatzResearch.WordTrace tailWord_5768615 prefixEnd_5768615 2962072205736053000983129 := by
  unfold tailWord_5768615
  simp only [CollatzResearch.WordTrace]
  refine ⟨210398673996300530851251299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140265782664200353900834199 210398673996300530851251299)
  ·
    refine ⟨315598010994450796276876949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210398673996300530851251299 315598010994450796276876949)
    ·
      refine ⟨14793656765364881075478607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 315598010994450796276876949 14793656765364881075478607)
      ·
        refine ⟨22190485148047321613217911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14793656765364881075478607 22190485148047321613217911)
        ·
          refine ⟨33285727722070982419826867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22190485148047321613217911 33285727722070982419826867)
          ·
            refine ⟨49928591583106473629740301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33285727722070982419826867 49928591583106473629740301)
            ·
              refine ⟨18723221843664927611152613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49928591583106473629740301 18723221843664927611152613)
              ·
                refine ⟨3510604095687173927091115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18723221843664927611152613 3510604095687173927091115)
                ·
                  refine ⟨5265906143530760890636673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510604095687173927091115 5265906143530760890636673)
                  ·
                    refine ⟨3949429607648070667977505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5265906143530760890636673 3949429607648070667977505)
                    ·
                      refine ⟨2962072205736053000983129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949429607648070667977505 2962072205736053000983129)
                      ·
                        rfl

theorem cell23_5768615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_5768615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768615 prefixEnd_5768615 := by exact prefixLift 5768615
  have htrace : WordTrace (prefixWord ++ tailWord_5768615) baseStart_5768615 baseEnd_5768615 := by
    simpa [prefixWord, tailWord_5768615, baseEnd_5768615] using wordTrace_append hprefix tailTrace_5768615
  have hstable : (prefixWord ++ tailWord_5768615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768615).length < 2 ^ (prefixWord ++ tailWord_5768615).sum := by decide
  have hdescent : baseEnd_5768615 < baseStart_5768615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768621 : List Nat := [1, 5, 2, 2, 1, 3, 1, 8]
def baseStart_5768621 : Nat := 118140960795 + 5768621 * 2 ^ 59
def prefixEnd_5768621 : Nat := 4983230072969 + 3 ^ 40 * 5768621 * 2
def baseEnd_5768621 : Nat := 109706492097036295463263

theorem tailTrace_5768621 : CollatzResearch.WordTrace tailWord_5768621 prefixEnd_5768621 109706492097036295463263 := by
  unfold tailWord_5768621
  simp only [CollatzResearch.WordTrace]
  refine ⟨210398892834278793875969717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140265928556185862583979811 210398892834278793875969717)
  ·
    refine ⟨19724896203213636925872161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210398892834278793875969717 19724896203213636925872161)
    ·
      refine ⟨14793672152410227694404121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19724896203213636925872161 14793672152410227694404121)
      ·
        refine ⟨11095254114307670770803091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14793672152410227694404121 11095254114307670770803091)
        ·
          refine ⟨16642881171461506156204637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11095254114307670770803091 16642881171461506156204637)
          ·
            refine ⟨6241080439298064808576739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16642881171461506156204637 6241080439298064808576739)
            ·
              refine ⟨9361620658947097212865109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6241080439298064808576739 9361620658947097212865109)
              ·
                refine ⟨109706492097036295463263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9361620658947097212865109 109706492097036295463263)
                ·
                  rfl

theorem cell23_5768621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 8].length) (baseStart_5768621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768621 prefixEnd_5768621 := by exact prefixLift 5768621
  have htrace : WordTrace (prefixWord ++ tailWord_5768621) baseStart_5768621 baseEnd_5768621 := by
    simpa [prefixWord, tailWord_5768621, baseEnd_5768621] using wordTrace_append hprefix tailTrace_5768621
  have hstable : (prefixWord ++ tailWord_5768621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768621).length < 2 ^ (prefixWord ++ tailWord_5768621).sum := by decide
  have hdescent : baseEnd_5768621 < baseStart_5768621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768631 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_5768631 : Nat := 118140960795 + 5768631 * 2 ^ 59
def prefixEnd_5768631 : Nat := 4983230072969 + 3 ^ 40 * 5768631 * 2
def baseEnd_5768631 : Nat := 2962080421426524938383055

theorem tailTrace_5768631 : CollatzResearch.WordTrace tailWord_5768631 prefixEnd_5768631 2962080421426524938383055 := by
  unfold tailWord_5768631
  simp only [CollatzResearch.WordTrace]
  refine ⟨210399257564242565583833747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140266171709495043722555831 210399257564242565583833747)
  ·
    refine ⟨315598886346363848375750621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210399257564242565583833747 315598886346363848375750621)
    ·
      refine ⟨118349582379886443140906483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315598886346363848375750621 118349582379886443140906483)
      ·
        refine ⟨177524373569829664711359725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118349582379886443140906483 177524373569829664711359725)
        ·
          refine ⟨66571640088686124266759897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177524373569829664711359725 66571640088686124266759897)
          ·
            refine ⟨49928730066514593200069923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66571640088686124266759897 49928730066514593200069923)
            ·
              refine ⟨74893095099771889800104885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49928730066514593200069923 74893095099771889800104885)
              ·
                refine ⟨7021227665603614668759833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74893095099771889800104885 7021227665603614668759833)
                ·
                  refine ⟨5265920749202711001569875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7021227665603614668759833 5265920749202711001569875)
                  ·
                    refine ⟨7898881123804066502354813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5265920749202711001569875 7898881123804066502354813)
                    ·
                      refine ⟨2962080421426524938383055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7898881123804066502354813 2962080421426524938383055)
                      ·
                        rfl

theorem cell23_5768631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_5768631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768631 prefixEnd_5768631 := by exact prefixLift 5768631
  have htrace : WordTrace (prefixWord ++ tailWord_5768631) baseStart_5768631 baseEnd_5768631 := by
    simpa [prefixWord, tailWord_5768631, baseEnd_5768631] using wordTrace_append hprefix tailTrace_5768631
  have hstable : (prefixWord ++ tailWord_5768631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768631).length < 2 ^ (prefixWord ++ tailWord_5768631).sum := by decide
  have hdescent : baseEnd_5768631 < baseStart_5768631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768647 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 1, 8]
def baseStart_5768647 : Nat := 118140960795 + 5768647 * 2 ^ 59
def prefixEnd_5768647 : Nat := 4983230072969 + 3 ^ 40 * 5768647 * 2
def baseEnd_5768647 : Nat := 987362879038998958594327

theorem tailTrace_5768647 : CollatzResearch.WordTrace tailWord_5768647 prefixEnd_5768647 987362879038998958594327 := by
  unfold tailWord_5768647
  simp only [CollatzResearch.WordTrace]
  refine ⟨210399841132184600316416195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140266560754789733544277463 210399841132184600316416195)
  ·
    refine ⟨315599761698276900474624293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210399841132184600316416195 315599761698276900474624293)
    ·
      refine ⟨59174955318426918838992055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315599761698276900474624293 59174955318426918838992055)
      ·
        refine ⟨88762432977640378258488083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59174955318426918838992055 88762432977640378258488083)
        ·
          refine ⟨133143649466460567387732125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88762432977640378258488083 133143649466460567387732125)
          ·
            refine ⟨49928868549922712770399547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133143649466460567387732125 49928868549922712770399547)
            ·
              refine ⟨74893302824884069155599321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49928868549922712770399547 74893302824884069155599321)
              ·
                refine ⟨56169977118663051866699491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74893302824884069155599321 56169977118663051866699491)
                ·
                  refine ⟨84254965677994577800049237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56169977118663051866699491 84254965677994577800049237)
                  ·
                    refine ⟨987362879038998958594327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84254965677994577800049237 987362879038998958594327)
                    ·
                      rfl

theorem cell23_5768647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_5768647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768647 prefixEnd_5768647 := by exact prefixLift 5768647
  have htrace : WordTrace (prefixWord ++ tailWord_5768647) baseStart_5768647 baseEnd_5768647 := by
    simpa [prefixWord, tailWord_5768647, baseEnd_5768647] using wordTrace_append hprefix tailTrace_5768647
  have hstable : (prefixWord ++ tailWord_5768647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768647).length < 2 ^ (prefixWord ++ tailWord_5768647).sum := by decide
  have hdescent : baseEnd_5768647 < baseStart_5768647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768688 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 1, 4, 2]
def baseStart_5768688 : Nat := 118140960795 + 5768688 * 2 ^ 59
def prefixEnd_5768688 : Nat := 4983230072969 + 3 ^ 40 * 5768688 * 2
def baseEnd_5768688 : Nat := 2962109689823831215370293

theorem tailTrace_5768688 : CollatzResearch.WordTrace tailWord_5768688 prefixEnd_5768688 2962109689823831215370293 := by
  unfold tailWord_5768688
  simp only [CollatzResearch.WordTrace]
  refine ⟨105200668262518032159329359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140267557683357376212439145 105200668262518032159329359)
  ·
    refine ⟨157801002393777048238994039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105200668262518032159329359 157801002393777048238994039)
    ·
      refine ⟨236701503590665572358491059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157801002393777048238994039 236701503590665572358491059)
      ·
        refine ⟨355052255385998358537736589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236701503590665572358491059 355052255385998358537736589)
        ·
          refine ⟨133144595769749384451651221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355052255385998358537736589 133144595769749384451651221)
          ·
            refine ⟨6241152926707002396171151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133144595769749384451651221 6241152926707002396171151)
            ·
              refine ⟨9361729390060503594256727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6241152926707002396171151 9361729390060503594256727)
              ·
                refine ⟨14042594085090755391385091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9361729390060503594256727 14042594085090755391385091)
                ·
                  refine ⟨21063891127636133087077637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14042594085090755391385091 21063891127636133087077637)
                  ·
                    refine ⟨3949479586431774953827057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21063891127636133087077637 3949479586431774953827057)
                    ·
                      refine ⟨2962109689823831215370293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949479586431774953827057 2962109689823831215370293)
                      ·
                        rfl

theorem cell23_5768688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 4, 2].length) (baseStart_5768688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768688 prefixEnd_5768688 := by exact prefixLift 5768688
  have htrace : WordTrace (prefixWord ++ tailWord_5768688) baseStart_5768688 baseEnd_5768688 := by
    simpa [prefixWord, tailWord_5768688, baseEnd_5768688] using wordTrace_append hprefix tailTrace_5768688
  have hstable : (prefixWord ++ tailWord_5768688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768688).length < 2 ^ (prefixWord ++ tailWord_5768688).sum := by decide
  have hdescent : baseEnd_5768688 < baseStart_5768688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768728 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 7]
def baseStart_5768728 : Nat := 118140960795 + 5768728 * 2 ^ 59
def prefixEnd_5768728 : Nat := 4983230072969 + 3 ^ 40 * 5768728 * 2
def baseEnd_5768728 : Nat := 329125581005556784318901

theorem tailTrace_5768728 : CollatzResearch.WordTrace tailWord_5768728 prefixEnd_5768728 329125581005556784318901 := by
  unfold tailWord_5768728
  simp only [CollatzResearch.WordTrace]
  refine ⟨105201397722445575575057419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140268530296594100766743225 105201397722445575575057419)
  ·
    refine ⟨157802096583668363362586129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105201397722445575575057419 157802096583668363362586129)
    ·
      refine ⟨118351572437751272521939597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157802096583668363362586129 118351572437751272521939597)
      ·
        refine ⟨44381839664156727195727349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118351572437751272521939597 44381839664156727195727349)
        ·
          refine ⟨4160797468514693174599439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44381839664156727195727349 4160797468514693174599439)
          ·
            refine ⟨6241196202772039761899159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160797468514693174599439 6241196202772039761899159)
            ·
              refine ⟨9361794304158059642848739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6241196202772039761899159 9361794304158059642848739)
              ·
                refine ⟨14042691456237089464273109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9361794304158059642848739 14042691456237089464273109)
                ·
                  refine ⟨329125581005556784318901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14042691456237089464273109 329125581005556784318901)
                  ·
                    rfl

theorem cell23_5768728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 7].length) (baseStart_5768728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768728 prefixEnd_5768728 := by exact prefixLift 5768728
  have htrace : WordTrace (prefixWord ++ tailWord_5768728) baseStart_5768728 baseEnd_5768728 := by
    simpa [prefixWord, tailWord_5768728, baseEnd_5768728] using wordTrace_append hprefix tailTrace_5768728
  have hstable : (prefixWord ++ tailWord_5768728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768728).length < 2 ^ (prefixWord ++ tailWord_5768728).sum := by decide
  have hdescent : baseEnd_5768728 < baseStart_5768728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768739 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 2, 2, 2]
def baseStart_5768739 : Nat := 118140960795 + 5768739 * 2 ^ 59
def prefixEnd_5768739 : Nat := 4983230072969 + 3 ^ 40 * 5768739 * 2
def baseEnd_5768739 : Nat := 2962135877337210515832559

theorem tailTrace_5768739 : CollatzResearch.WordTrace tailWord_5768739 prefixEnd_5768739 2962135877337210515832559 := by
  unfold tailWord_5768739
  simp only [CollatzResearch.WordTrace]
  refine ⟨210403196647851300028765271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140268797765234200019176847 210403196647851300028765271)
  ·
    refine ⟨315604794971776950043147907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210403196647851300028765271 315604794971776950043147907)
    ·
      refine ⟨473407192457665425064721861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315604794971776950043147907 473407192457665425064721861)
      ·
        refine ⟨88763848585812267199635349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 473407192457665425064721861 88763848585812267199635349)
        ·
          refine ⟨4160805402459950024982907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88763848585812267199635349 4160805402459950024982907)
          ·
            refine ⟨6241208103689925037474361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160805402459950024982907 6241208103689925037474361)
            ·
              refine ⟨4680906077767443778105771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6241208103689925037474361 4680906077767443778105771)
              ·
                refine ⟨7021359116651165667158657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680906077767443778105771 7021359116651165667158657)
                ·
                  refine ⟨5266019337488374250368993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7021359116651165667158657 5266019337488374250368993)
                  ·
                    refine ⟨3949514503116280687776745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5266019337488374250368993 3949514503116280687776745)
                    ·
                      refine ⟨2962135877337210515832559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949514503116280687776745 2962135877337210515832559)
                      ·
                        rfl

theorem cell23_5768739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_5768739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768739 prefixEnd_5768739 := by exact prefixLift 5768739
  have htrace : WordTrace (prefixWord ++ tailWord_5768739) baseStart_5768739 baseEnd_5768739 := by
    simpa [prefixWord, tailWord_5768739, baseEnd_5768739] using wordTrace_append hprefix tailTrace_5768739
  have hstable : (prefixWord ++ tailWord_5768739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768739).length < 2 ^ (prefixWord ++ tailWord_5768739).sum := by decide
  have hdescent : baseEnd_5768739 < baseStart_5768739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768761 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5768761 : Nat := 118140960795 + 5768761 * 2 ^ 59
def prefixEnd_5768761 : Nat := 4983230072969 + 3 ^ 40 * 5768761 * 2
def baseEnd_5768761 : Nat := 2962147173911609429757457

theorem tailTrace_5768761 : CollatzResearch.WordTrace tailWord_5768761 prefixEnd_5768761 2962147173911609429757457 := by
  unfold tailWord_5768761
  simp only [CollatzResearch.WordTrace]
  refine ⟨210403999053771597786066137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140269332702514398524044091 210403999053771597786066137)
  ·
    refine ⟨157802999290328698339549603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210403999053771597786066137 157802999290328698339549603)
    ·
      refine ⟨236704498935493047509324405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157802999290328698339549603 236704498935493047509324405)
      ·
        refine ⟨22191046775202473203999163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 236704498935493047509324405 22191046775202473203999163)
        ·
          refine ⟨33286570162803709805998745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22191046775202473203999163 33286570162803709805998745)
          ·
            refine ⟨24964927622102782354499059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33286570162803709805998745 24964927622102782354499059)
            ·
              refine ⟨37447391433154173531748589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24964927622102782354499059 37447391433154173531748589)
              ·
                refine ⟨14042771787432815074405721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37447391433154173531748589 14042771787432815074405721)
                ·
                  refine ⟨10532078840574611305804291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14042771787432815074405721 10532078840574611305804291)
                  ·
                    refine ⟨15798118260861916958706437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10532078840574611305804291 15798118260861916958706437)
                    ·
                      refine ⟨2962147173911609429757457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15798118260861916958706437 2962147173911609429757457)
                      ·
                        rfl

theorem cell23_5768761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5768761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768761 prefixEnd_5768761 := by exact prefixLift 5768761
  have htrace : WordTrace (prefixWord ++ tailWord_5768761) baseStart_5768761 baseEnd_5768761 := by
    simpa [prefixWord, tailWord_5768761, baseEnd_5768761] using wordTrace_append hprefix tailTrace_5768761
  have hstable : (prefixWord ++ tailWord_5768761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768761).length < 2 ^ (prefixWord ++ tailWord_5768761).sum := by decide
  have hdescent : baseEnd_5768761 < baseStart_5768761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768822 : List Nat := [5, 1, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_5768822 : Nat := 118140960795 + 5768822 * 2 ^ 59
def prefixEnd_5768822 : Nat := 4983230072969 + 3 ^ 40 * 5768822 * 2
def baseEnd_5768822 : Nat := 987392832077177897031559

theorem tailTrace_5768822 : CollatzResearch.WordTrace tailWord_5768822 prefixEnd_5768822 987392832077177897031559 := by
  unfold tailWord_5768822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13150388994159412825252295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140270815937700403469357813 13150388994159412825252295)
  ·
    refine ⟨19725583491239119237878443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13150388994159412825252295 19725583491239119237878443)
    ·
      refine ⟨29588375236858678856817665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19725583491239119237878443 29588375236858678856817665)
      ·
        refine ⟨22191281427644009142613249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29588375236858678856817665 22191281427644009142613249)
        ·
          refine ⟨16643461070733006856959937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22191281427644009142613249 16643461070733006856959937)
          ·
            refine ⟨12482595803049755142719953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16643461070733006856959937 12482595803049755142719953)
            ·
              refine ⟨9361946852287316357039965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12482595803049755142719953 9361946852287316357039965)
              ·
                refine ⟨3510730069607743633889987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9361946852287316357039965 3510730069607743633889987)
                ·
                  refine ⟨5266095104411615450834981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510730069607743633889987 5266095104411615450834981)
                  ·
                    refine ⟨987392832077177897031559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5266095104411615450834981 987392832077177897031559)
                    ·
                      rfl

theorem cell23_5768822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_5768822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768822 prefixEnd_5768822 := by exact prefixLift 5768822
  have htrace : WordTrace (prefixWord ++ tailWord_5768822) baseStart_5768822 baseEnd_5768822 := by
    simpa [prefixWord, tailWord_5768822, baseEnd_5768822] using wordTrace_append hprefix tailTrace_5768822
  have hstable : (prefixWord ++ tailWord_5768822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768822).length < 2 ^ (prefixWord ++ tailWord_5768822).sum := by decide
  have hdescent : baseEnd_5768822 < baseStart_5768822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768851 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 4, 6, 2]
def baseStart_5768851 : Nat := 118140960795 + 5768851 * 2 ^ 59
def prefixEnd_5768851 : Nat := 4983230072969 + 3 ^ 40 * 5768851 * 2
def baseEnd_5768851 : Nat := 2962193387170514077632043

theorem tailTrace_5768851 : CollatzResearch.WordTrace tailWord_5768851 prefixEnd_5768851 2962193387170514077632043 := by
  unfold tailWord_5768851
  simp only [CollatzResearch.WordTrace]
  refine ⟨210407281623445543156842407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140271521082297028771228271 210407281623445543156842407)
  ·
    refine ⟨315610922435168314735263611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210407281623445543156842407 315610922435168314735263611)
    ·
      refine ⟨473416383652752472102895417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315610922435168314735263611 473416383652752472102895417)
      ·
        refine ⟨355062287739564354077171563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473416383652752472102895417 355062287739564354077171563)
        ·
          refine ⟨532593431609346531115757345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355062287739564354077171563 532593431609346531115757345)
          ·
            refine ⟨399445073707009898336818009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532593431609346531115757345 399445073707009898336818009)
            ·
              refine ⟨299583805280257423752613507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399445073707009898336818009 299583805280257423752613507)
              ·
                refine ⟨449375707920386135628920261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299583805280257423752613507 449375707920386135628920261)
                ·
                  refine ⟨84257945235072400430422549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449375707920386135628920261 84257945235072400430422549)
                  ·
                    refine ⟨3949591182894018770176057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84257945235072400430422549 3949591182894018770176057)
                    ·
                      refine ⟨2962193387170514077632043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949591182894018770176057 2962193387170514077632043)
                      ·
                        rfl

theorem cell23_5768851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 6, 2].length) (baseStart_5768851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768851 prefixEnd_5768851 := by exact prefixLift 5768851
  have htrace : WordTrace (prefixWord ++ tailWord_5768851) baseStart_5768851 baseEnd_5768851 := by
    simpa [prefixWord, tailWord_5768851, baseEnd_5768851] using wordTrace_append hprefix tailTrace_5768851
  have hstable : (prefixWord ++ tailWord_5768851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768851).length < 2 ^ (prefixWord ++ tailWord_5768851).sum := by decide
  have hdescent : baseEnd_5768851 < baseStart_5768851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768868 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_5768868 : Nat := 118140960795 + 5768868 * 2 ^ 59
def prefixEnd_5768868 : Nat := 4983230072969 + 3 ^ 40 * 5768868 * 2
def baseEnd_5768868 : Nat := 2962202116341640511119465

theorem tailTrace_5768868 : CollatzResearch.WordTrace tailWord_5768868 prefixEnd_5768868 2962202116341640511119465 := by
  unfold tailWord_5768868
  simp only [CollatzResearch.WordTrace]
  refine ⟨105203950832191977530105629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140271934442922636706807505 105203950832191977530105629)
  ·
    refine ⟨39451481562071991573789611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105203950832191977530105629 39451481562071991573789611)
    ·
      refine ⟨59177222343107987360684417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39451481562071991573789611 59177222343107987360684417)
      ·
        refine ⟨44382916757330990520513313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59177222343107987360684417 44382916757330990520513313)
        ·
          refine ⟨33287187567998242890384985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44382916757330990520513313 33287187567998242890384985)
          ·
            refine ⟨24965390675998682167788739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33287187567998242890384985 24965390675998682167788739)
            ·
              refine ⟨37448086013998023251683109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24965390675998682167788739 37448086013998023251683109)
              ·
                refine ⟨7021516127624629359690583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37448086013998023251683109 7021516127624629359690583)
                ·
                  refine ⟨10532274191436944039535875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021516127624629359690583 10532274191436944039535875)
                  ·
                    refine ⟨15798411287155416059303813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10532274191436944039535875 15798411287155416059303813)
                    ·
                      refine ⟨2962202116341640511119465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15798411287155416059303813 2962202116341640511119465)
                      ·
                        rfl

theorem cell23_5768868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_5768868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768868 prefixEnd_5768868 := by exact prefixLift 5768868
  have htrace : WordTrace (prefixWord ++ tailWord_5768868) baseStart_5768868 baseEnd_5768868 := by
    simpa [prefixWord, tailWord_5768868, baseEnd_5768868] using wordTrace_append hprefix tailTrace_5768868
  have hstable : (prefixWord ++ tailWord_5768868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768868).length < 2 ^ (prefixWord ++ tailWord_5768868).sum := by decide
  have hdescent : baseEnd_5768868 < baseStart_5768868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768901 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_5768901 : Nat := 118140960795 + 5768901 * 2 ^ 59
def prefixEnd_5768901 : Nat := 4983230072969 + 3 ^ 40 * 5768901 * 2
def baseEnd_5768901 : Nat := 2962219061203238882006813

theorem tailTrace_5768901 : CollatzResearch.WordTrace tailWord_5768901 prefixEnd_5768901 2962219061203238882006813 := by
  unfold tailWord_5768901
  simp only [CollatzResearch.WordTrace]
  refine ⟨210409105273264401696162557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140272736848842934464108371 210409105273264401696162557)
  ·
    refine ⟨78903414477474150636060959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210409105273264401696162557 78903414477474150636060959)
    ·
      refine ⟨118355121716211225954091439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78903414477474150636060959 118355121716211225954091439)
      ·
        refine ⟨177532682574316838931137159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118355121716211225954091439 177532682574316838931137159)
        ·
          refine ⟨266299023861475258396705739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177532682574316838931137159 266299023861475258396705739)
          ·
            refine ⟨399448535792212887595058609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266299023861475258396705739 399448535792212887595058609)
            ·
              refine ⟨299586401844159665696293957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399448535792212887595058609 299586401844159665696293957)
              ·
                refine ⟨56172450345779937318055117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299586401844159665696293957 56172450345779937318055117)
                ·
                  refine ⟨21064668879667476494270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56172450345779937318055117 21064668879667476494270669)
                  ·
                    refine ⟨7899250829875303685351501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21064668879667476494270669 7899250829875303685351501)
                    ·
                      refine ⟨2962219061203238882006813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7899250829875303685351501 2962219061203238882006813)
                      ·
                        rfl

theorem cell23_5768901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_5768901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768901 prefixEnd_5768901 := by exact prefixLift 5768901
  have htrace : WordTrace (prefixWord ++ tailWord_5768901) baseStart_5768901 baseEnd_5768901 := by
    simpa [prefixWord, tailWord_5768901, baseEnd_5768901] using wordTrace_append hprefix tailTrace_5768901
  have hstable : (prefixWord ++ tailWord_5768901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768901).length < 2 ^ (prefixWord ++ tailWord_5768901).sum := by decide
  have hdescent : baseEnd_5768901 < baseStart_5768901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768908 : List Nat := [2, 2, 1, 5, 2, 1, 2, 8]
def baseStart_5768908 : Nat := 118140960795 + 5768908 * 2 ^ 59
def prefixEnd_5768908 : Nat := 4983230072969 + 3 ^ 40 * 5768908 * 2
def baseEnd_5768908 : Nat := 109711950206215568689603

theorem tailTrace_5768908 : CollatzResearch.WordTrace tailWord_5768908 prefixEnd_5768908 109711950206215568689603 := by
  unfold tailWord_5768908
  simp only [CollatzResearch.WordTrace]
  refine ⟨105204680292119520945833689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140272907056159361261111585 105204680292119520945833689)
  ·
    refine ⟨78903510219089640709375267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105204680292119520945833689 78903510219089640709375267)
    ·
      refine ⟨118355265328634461064062901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78903510219089640709375267 118355265328634461064062901)
      ·
        refine ⟨11095806124559480724755897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118355265328634461064062901 11095806124559480724755897)
        ·
          refine ⟨8321854593419610543566923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11095806124559480724755897 8321854593419610543566923)
          ·
            refine ⟨12482781890129415815350385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8321854593419610543566923 12482781890129415815350385)
            ·
              refine ⟨9362086417597061861512789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12482781890129415815350385 9362086417597061861512789)
              ·
                refine ⟨109711950206215568689603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9362086417597061861512789 109711950206215568689603)
                ·
                  rfl

theorem cell23_5768908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 8].length) (baseStart_5768908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768908 prefixEnd_5768908 := by exact prefixLift 5768908
  have htrace : WordTrace (prefixWord ++ tailWord_5768908) baseStart_5768908 baseEnd_5768908 := by
    simpa [prefixWord, tailWord_5768908, baseEnd_5768908] using wordTrace_append hprefix tailTrace_5768908
  have hstable : (prefixWord ++ tailWord_5768908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768908).length < 2 ^ (prefixWord ++ tailWord_5768908).sum := by decide
  have hdescent : baseEnd_5768908 < baseStart_5768908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768961 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_5768961 : Nat := 118140960795 + 5768961 * 2 ^ 59
def prefixEnd_5768961 : Nat := 4983230072969 + 3 ^ 40 * 5768961 * 2
def baseEnd_5768961 : Nat := 2962249870042508647256537

theorem tailTrace_5768961 : CollatzResearch.WordTrace tailWord_5768961 prefixEnd_5768961 2962249870042508647256537 := by
  unfold tailWord_5768961
  simp only [CollatzResearch.WordTrace]
  refine ⟨210411293653047031943346737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140274195768698021295564491 210411293653047031943346737)
  ·
    refine ⟨157808470239785273957510053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210411293653047031943346737 157808470239785273957510053)
    ·
      refine ⟨29589088169959738867033135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157808470239785273957510053 29589088169959738867033135)
      ·
        refine ⟨44383632254939608300549703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29589088169959738867033135 44383632254939608300549703)
        ·
          refine ⟨66575448382409412450824555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44383632254939608300549703 66575448382409412450824555)
          ·
            refine ⟨99863172573614118676236833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66575448382409412450824555 99863172573614118676236833)
            ·
              refine ⟨74897379430210589007177625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99863172573614118676236833 74897379430210589007177625)
              ·
                refine ⟨56173034572657941755383219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74897379430210589007177625 56173034572657941755383219)
                ·
                  refine ⟨84259551858986912633074829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56173034572657941755383219 84259551858986912633074829)
                  ·
                    refine ⟨31597331947120092237403061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84259551858986912633074829 31597331947120092237403061)
                    ·
                      refine ⟨2962249870042508647256537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31597331947120092237403061 2962249870042508647256537)
                      ·
                        rfl

theorem cell23_5768961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_5768961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768961 prefixEnd_5768961 := by exact prefixLift 5768961
  have htrace : WordTrace (prefixWord ++ tailWord_5768961) baseStart_5768961 baseEnd_5768961 := by
    simpa [prefixWord, tailWord_5768961, baseEnd_5768961] using wordTrace_append hprefix tailTrace_5768961
  have hstable : (prefixWord ++ tailWord_5768961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768961).length < 2 ^ (prefixWord ++ tailWord_5768961).sum := by decide
  have hdescent : baseEnd_5768961 < baseStart_5768961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768971 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 4]
def baseStart_5768971 : Nat := 118140960795 + 5768971 * 2 ^ 59
def prefixEnd_5768971 : Nat := 4983230072969 + 3 ^ 40 * 5768971 * 2
def baseEnd_5768971 : Nat := 2962255004849053608131491

theorem tailTrace_5768971 : CollatzResearch.WordTrace tailWord_5768971 prefixEnd_5768971 2962255004849053608131491 := by
  unfold tailWord_5768971
  simp only [CollatzResearch.WordTrace]
  refine ⟨210411658383010803651210767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140274438922007202434140511 210411658383010803651210767)
  ·
    refine ⟨315617487574516205476816151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210411658383010803651210767 315617487574516205476816151)
    ·
      refine ⟨473426231361774308215224227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315617487574516205476816151 473426231361774308215224227)
      ·
        refine ⟨710139347042661462322836341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473426231361774308215224227 710139347042661462322836341)
        ·
          refine ⟨66575563785249512092765907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 710139347042661462322836341 66575563785249512092765907)
          ·
            refine ⟨99863345677874268139148861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66575563785249512092765907 99863345677874268139148861)
            ·
              refine ⟨37448754629202850552180823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99863345677874268139148861 37448754629202850552180823)
              ·
                refine ⟨56173131943804275828271235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37448754629202850552180823 56173131943804275828271235)
                ·
                  refine ⟨84259697915706413742406853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56173131943804275828271235 84259697915706413742406853)
                  ·
                    refine ⟨15798693359194952576701285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84259697915706413742406853 15798693359194952576701285)
                    ·
                      refine ⟨2962255004849053608131491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15798693359194952576701285 2962255004849053608131491)
                      ·
                        rfl

theorem cell23_5768971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 4].length) (baseStart_5768971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768971 prefixEnd_5768971 := by exact prefixLift 5768971
  have htrace : WordTrace (prefixWord ++ tailWord_5768971) baseStart_5768971 baseEnd_5768971 := by
    simpa [prefixWord, tailWord_5768971, baseEnd_5768971] using wordTrace_append hprefix tailTrace_5768971
  have hstable : (prefixWord ++ tailWord_5768971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768971).length < 2 ^ (prefixWord ++ tailWord_5768971).sum := by decide
  have hdescent : baseEnd_5768971 < baseStart_5768971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5768981 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 9]
def baseStart_5768981 : Nat := 118140960795 + 5768981 * 2 ^ 59
def prefixEnd_5768981 : Nat := 4983230072969 + 3 ^ 40 * 5768981 * 2
def baseEnd_5768981 : Nat := 329140015517288729889605

theorem tailTrace_5768981 : CollatzResearch.WordTrace tailWord_5768981 prefixEnd_5768981 329140015517288729889605 := by
  unfold tailWord_5768981
  simp only [CollatzResearch.WordTrace]
  refine ⟨210412023112974575359074797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140274682075316383572716531 210412023112974575359074797)
  ·
    refine ⟨78904508667365465759653049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210412023112974575359074797 78904508667365465759653049)
    ·
      refine ⟨59178381500524099319739787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78904508667365465759653049 59178381500524099319739787)
      ·
        refine ⟨88767572250786148979609681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59178381500524099319739787 88767572250786148979609681)
        ·
          refine ⟨66575679188089611734707261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88767572250786148979609681 66575679188089611734707261)
          ·
            refine ⟨24965879695533604400515223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66575679188089611734707261 24965879695533604400515223)
            ·
              refine ⟨37448819543300406600772835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24965879695533604400515223 37448819543300406600772835)
              ·
                refine ⟨56173229314950609901159253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37448819543300406600772835 56173229314950609901159253)
                ·
                  refine ⟨329140015517288729889605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56173229314950609901159253 329140015517288729889605)
                  ·
                    rfl

theorem cell23_5768981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_5768981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5768981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5768981 prefixEnd_5768981 := by exact prefixLift 5768981
  have htrace : WordTrace (prefixWord ++ tailWord_5768981) baseStart_5768981 baseEnd_5768981 := by
    simpa [prefixWord, tailWord_5768981, baseEnd_5768981] using wordTrace_append hprefix tailTrace_5768981
  have hstable : (prefixWord ++ tailWord_5768981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5768981).length < 2 ^ (prefixWord ++ tailWord_5768981).sum := by decide
  have hdescent : baseEnd_5768981 < baseStart_5768981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5768981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769009 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 2, 2, 2]
def baseStart_5769009 : Nat := 118140960795 + 5769009 * 2 ^ 59
def prefixEnd_5769009 : Nat := 4983230072969 + 3 ^ 40 * 5769009 * 2
def baseEnd_5769009 : Nat := 2962274517113924459456317

theorem tailTrace_5769009 : CollatzResearch.WordTrace tailWord_5769009 prefixEnd_5769009 2962274517113924459456317 := by
  unfold tailWord_5769009
  simp only [CollatzResearch.WordTrace]
  refine ⟨210413044356873136141094081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140275362904582090760729387 210413044356873136141094081)
  ·
    refine ⟨157809783267654852105820561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210413044356873136141094081 157809783267654852105820561)
    ·
      refine ⟨118357337450741139079365421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157809783267654852105820561 118357337450741139079365421)
      ·
        refine ⟨44384001544027927154762033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118357337450741139079365421 44384001544027927154762033)
        ·
          refine ⟨33288001158020945366071525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44384001544027927154762033 33288001158020945366071525)
          ·
            refine ⟨6241500217128927256138411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33288001158020945366071525 6241500217128927256138411)
            ·
              refine ⟨9362250325693390884207617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6241500217128927256138411 9362250325693390884207617)
              ·
                refine ⟨7021687744270043163155713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9362250325693390884207617 7021687744270043163155713)
                ·
                  refine ⟨5266265808202532372366785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7021687744270043163155713 5266265808202532372366785)
                  ·
                    refine ⟨3949699356151899279275089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5266265808202532372366785 3949699356151899279275089)
                    ·
                      refine ⟨2962274517113924459456317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949699356151899279275089 2962274517113924459456317)
                      ·
                        rfl

theorem cell23_5769009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_5769009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769009 prefixEnd_5769009 := by exact prefixLift 5769009
  have htrace : WordTrace (prefixWord ++ tailWord_5769009) baseStart_5769009 baseEnd_5769009 := by
    simpa [prefixWord, tailWord_5769009, baseEnd_5769009] using wordTrace_append hprefix tailTrace_5769009
  have hstable : (prefixWord ++ tailWord_5769009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769009).length < 2 ^ (prefixWord ++ tailWord_5769009).sum := by decide
  have hdescent : baseEnd_5769009 < baseStart_5769009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769088 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 6]
def baseStart_5769088 : Nat := 118140960795 + 5769088 * 2 ^ 59
def prefixEnd_5769088 : Nat := 4983230072969 + 3 ^ 40 * 5769088 * 2
def baseEnd_5769088 : Nat := 329146120231736627818717

theorem tailTrace_5769088 : CollatzResearch.WordTrace tailWord_5769088 prefixEnd_5769088 329146120231736627818717 := by
  unfold tailWord_5769088
  simp only [CollatzResearch.WordTrace]
  refine ⟨105207962861793466316609959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140277283815724621755479945 105207962861793466316609959)
  ·
    refine ⟨157811944292690199474914939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105207962861793466316609959 157811944292690199474914939)
    ·
      refine ⟨236717916439035299212372409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157811944292690199474914939 236717916439035299212372409)
      ·
        refine ⟨177538437329276474409279307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236717916439035299212372409 177538437329276474409279307)
        ·
          refine ⟨266307655993914711613918961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177538437329276474409279307 266307655993914711613918961)
          ·
            refine ⟨199730741995436033710439221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266307655993914711613918961 199730741995436033710439221)
            ·
              refine ⟨18724757062072128160353677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199730741995436033710439221 18724757062072128160353677)
              ·
                refine ⟨7021783898277048060132629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18724757062072128160353677 7021783898277048060132629)
                ·
                  refine ⟨329146120231736627818717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7021783898277048060132629 329146120231736627818717)
                  ·
                    rfl

theorem cell23_5769088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 6].length) (baseStart_5769088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769088 prefixEnd_5769088 := by exact prefixLift 5769088
  have htrace : WordTrace (prefixWord ++ tailWord_5769088) baseStart_5769088 baseEnd_5769088 := by
    simpa [prefixWord, tailWord_5769088, baseEnd_5769088] using wordTrace_append hprefix tailTrace_5769088
  have hstable : (prefixWord ++ tailWord_5769088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769088).length < 2 ^ (prefixWord ++ tailWord_5769088).sum := by decide
  have hdescent : baseEnd_5769088 < baseStart_5769088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769122 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 6]
def baseStart_5769122 : Nat := 118140960795 + 5769122 * 2 ^ 59
def prefixEnd_5769122 : Nat := 4983230072969 + 3 ^ 40 * 5769122 * 2
def baseEnd_5769122 : Nat := 329148060047542501927033

theorem tailTrace_5769122 : CollatzResearch.WordTrace tailWord_5769122 prefixEnd_5769122 329148060047542501927033 := by
  unfold tailWord_5769122
  simp only [CollatzResearch.WordTrace]
  refine ⟨52604291451365939109989405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140278110536975837626638413 52604291451365939109989405)
  ·
    refine ⟨19726609294262227166246027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52604291451365939109989405 19726609294262227166246027)
    ·
      refine ⟨29589913941393340749369041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19726609294262227166246027 29589913941393340749369041)
      ·
        refine ⟨22192435456045005562026781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29589913941393340749369041 22192435456045005562026781)
        ·
          refine ⟨8322163296016877085760043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22192435456045005562026781 8322163296016877085760043)
          ·
            refine ⟨12483244944025315628640065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8322163296016877085760043 12483244944025315628640065)
            ·
              refine ⟨9362433708018986721480049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12483244944025315628640065 9362433708018986721480049)
              ·
                refine ⟨7021825281014240041110037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9362433708018986721480049 7021825281014240041110037)
                ·
                  refine ⟨329148060047542501927033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7021825281014240041110037 329148060047542501927033)
                  ·
                    rfl

theorem cell23_5769122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_5769122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769122 prefixEnd_5769122 := by exact prefixLift 5769122
  have htrace : WordTrace (prefixWord ++ tailWord_5769122) baseStart_5769122 baseEnd_5769122 := by
    simpa [prefixWord, tailWord_5769122, baseEnd_5769122] using wordTrace_append hprefix tailTrace_5769122
  have hstable : (prefixWord ++ tailWord_5769122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769122).length < 2 ^ (prefixWord ++ tailWord_5769122).sum := by decide
  have hdescent : baseEnd_5769122 < baseStart_5769122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769172 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_5769172 : Nat := 118140960795 + 5769172 * 2 ^ 59
def prefixEnd_5769172 : Nat := 4983230072969 + 3 ^ 40 * 5769172 * 2
def baseEnd_5769172 : Nat := 2962358214460607321718067

theorem tailTrace_5769172 : CollatzResearch.WordTrace tailWord_5769172 prefixEnd_5769172 2962358214460607321718067 := by
  unfold tailWord_5769172
  simp only [CollatzResearch.WordTrace]
  refine ⟨105209494727641307489638885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140279326303521743319518513 105209494727641307489638885)
  ·
    refine ⟨19726780261432745154307291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105209494727641307489638885 19726780261432745154307291)
    ·
      refine ⟨29590170392149117731460937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19726780261432745154307291 29590170392149117731460937)
      ·
        refine ⟨22192627794111838298595703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29590170392149117731460937 22192627794111838298595703)
        ·
          refine ⟨33288941691167757447893555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22192627794111838298595703 33288941691167757447893555)
          ·
            refine ⟨49933412536751636171840333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33288941691167757447893555 49933412536751636171840333)
            ·
              refine ⟨18725029701281863564440125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49933412536751636171840333 18725029701281863564440125)
              ·
                refine ⟨7021886137980698836665047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18725029701281863564440125 7021886137980698836665047)
                ·
                  refine ⟨10532829206971048254997571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021886137980698836665047 10532829206971048254997571)
                  ·
                    refine ⟨15799243810456572382496357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10532829206971048254997571 15799243810456572382496357)
                    ·
                      refine ⟨2962358214460607321718067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15799243810456572382496357 2962358214460607321718067)
                      ·
                        rfl

theorem cell23_5769172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_5769172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769172 prefixEnd_5769172 := by exact prefixLift 5769172
  have htrace : WordTrace (prefixWord ++ tailWord_5769172) baseStart_5769172 baseEnd_5769172 := by
    simpa [prefixWord, tailWord_5769172, baseEnd_5769172] using wordTrace_append hprefix tailTrace_5769172
  have hstable : (prefixWord ++ tailWord_5769172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769172).length < 2 ^ (prefixWord ++ tailWord_5769172).sum := by decide
  have hdescent : baseEnd_5769172 < baseStart_5769172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769208 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 2, 7]
def baseStart_5769208 : Nat := 118140960795 + 5769208 * 2 ^ 59
def prefixEnd_5769208 : Nat := 4983230072969 + 3 ^ 40 * 5769208 * 2
def baseEnd_5769208 : Nat := 987458899921389726955967

theorem tailTrace_5769208 : CollatzResearch.WordTrace tailWord_5769208 prefixEnd_5769208 987458899921389726955967 := by
  unfold tailWord_5769208
  simp only [CollatzResearch.WordTrace]
  refine ⟨105210151241576096563794139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140280201655434795418392185 105210151241576096563794139)
  ·
    refine ⟨157815226862364144845691209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105210151241576096563794139 157815226862364144845691209)
    ·
      refine ⟨118361420146773108634268407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157815226862364144845691209 118361420146773108634268407)
      ·
        refine ⟨177542130220159662951402611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118361420146773108634268407 177542130220159662951402611)
        ·
          refine ⟨266313195330239494427103917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177542130220159662951402611 266313195330239494427103917)
          ·
            refine ⟨99867448248839810410163969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266313195330239494427103917 99867448248839810410163969)
            ·
              refine ⟨74900586186629857807622977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99867448248839810410163969 74900586186629857807622977)
              ·
                refine ⟨56175439639972393355717233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74900586186629857807622977 56175439639972393355717233)
                ·
                  refine ⟨42131579729979295016787925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56175439639972393355717233 42131579729979295016787925)
                  ·
                    refine ⟨987458899921389726955967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42131579729979295016787925 987458899921389726955967)
                    ·
                      rfl

theorem cell23_5769208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_5769208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769208 prefixEnd_5769208 := by exact prefixLift 5769208
  have htrace : WordTrace (prefixWord ++ tailWord_5769208) baseStart_5769208 baseEnd_5769208 := by
    simpa [prefixWord, tailWord_5769208, baseEnd_5769208] using wordTrace_append hprefix tailTrace_5769208
  have hstable : (prefixWord ++ tailWord_5769208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769208).length < 2 ^ (prefixWord ++ tailWord_5769208).sum := by decide
  have hdescent : baseEnd_5769208 < baseStart_5769208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769215 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 2, 7, 2]
def baseStart_5769215 : Nat := 118140960795 + 5769215 * 2 ^ 59
def prefixEnd_5769215 : Nat := 4983230072969 + 3 ^ 40 * 5769215 * 2
def baseEnd_5769215 : Nat := 2962380294128750653480369

theorem tailTrace_5769215 : CollatzResearch.WordTrace tailWord_5769215 prefixEnd_5769215 2962380294128750653480369 := by
  unfold tailWord_5769215
  simp only [CollatzResearch.WordTrace]
  refine ⟨210420557794126833323093099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140280371862751222215395399 210420557794126833323093099)
  ·
    refine ⟨315630836691190249984639649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210420557794126833323093099 315630836691190249984639649)
    ·
      refine ⟨236723127518392687488479737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315630836691190249984639649 236723127518392687488479737)
      ·
        refine ⟨177542345638794515616359803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236723127518392687488479737 177542345638794515616359803)
        ·
          refine ⟨266313518458191773424539705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177542345638794515616359803 266313518458191773424539705)
          ·
            refine ⟨199735138843643830068404779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266313518458191773424539705 199735138843643830068404779)
            ·
              refine ⟨299602708265465745102607169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199735138843643830068404779 299602708265465745102607169)
              ·
                refine ⟨224702031199099308826955377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299602708265465745102607169 224702031199099308826955377)
                ·
                  refine ⟨168526523399324481620216533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224702031199099308826955377 168526523399324481620216533)
                  ·
                    refine ⟨3949840392171667537973825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168526523399324481620216533 3949840392171667537973825)
                    ·
                      refine ⟨2962380294128750653480369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949840392171667537973825 2962380294128750653480369)
                      ·
                        rfl

theorem cell23_5769215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_5769215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769215 prefixEnd_5769215 := by exact prefixLift 5769215
  have htrace : WordTrace (prefixWord ++ tailWord_5769215) baseStart_5769215 baseEnd_5769215 := by
    simpa [prefixWord, tailWord_5769215, baseEnd_5769215] using wordTrace_append hprefix tailTrace_5769215
  have hstable : (prefixWord ++ tailWord_5769215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769215).length < 2 ^ (prefixWord ++ tailWord_5769215).sum := by decide
  have hdescent : baseEnd_5769215 < baseStart_5769215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769223 : List Nat := [1, 1, 4, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_5769223 : Nat := 118140960795 + 5769223 * 2 ^ 59
def prefixEnd_5769223 : Nat := 4983230072969 + 3 ^ 40 * 5769223 * 2
def baseEnd_5769223 : Nat := 2962384401973986622180333

theorem tailTrace_5769223 : CollatzResearch.WordTrace tailWord_5769223 prefixEnd_5769223 2962384401973986622180333 := by
  unfold tailWord_5769223
  simp only [CollatzResearch.WordTrace]
  refine ⟨210420849578097850689384323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140280566385398567126256215 210420849578097850689384323)
  ·
    refine ⟨315631274367146776034076485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210420849578097850689384323 315631274367146776034076485)
    ·
      refine ⟨59180863943840020506389341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315631274367146776034076485 59180863943840020506389341)
      ·
        refine ⟨22192823978940007689896003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59180863943840020506389341 22192823978940007689896003)
        ·
          refine ⟨33289235968410011534844005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22192823978940007689896003 33289235968410011534844005)
          ·
            refine ⟨6241731744076877162783251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33289235968410011534844005 6241731744076877162783251)
            ·
              refine ⟨9362597616115315744174877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6241731744076877162783251 9362597616115315744174877)
              ·
                refine ⟨3510974106043243404065579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9362597616115315744174877 3510974106043243404065579)
                ·
                  refine ⟨5266461159064865106098369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510974106043243404065579 5266461159064865106098369)
                  ·
                    refine ⟨3949845869298648829573777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5266461159064865106098369 3949845869298648829573777)
                    ·
                      refine ⟨2962384401973986622180333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949845869298648829573777 2962384401973986622180333)
                      ·
                        rfl

theorem cell23_5769223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_5769223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769223 prefixEnd_5769223 := by exact prefixLift 5769223
  have htrace : WordTrace (prefixWord ++ tailWord_5769223) baseStart_5769223 baseEnd_5769223 := by
    simpa [prefixWord, tailWord_5769223, baseEnd_5769223] using wordTrace_append hprefix tailTrace_5769223
  have hstable : (prefixWord ++ tailWord_5769223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769223).length < 2 ^ (prefixWord ++ tailWord_5769223).sum := by decide
  have hdescent : baseEnd_5769223 < baseStart_5769223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769265 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_5769265 : Nat := 118140960795 + 5769265 * 2 ^ 59
def prefixEnd_5769265 : Nat := 4983230072969 + 3 ^ 40 * 5769265 * 2
def baseEnd_5769265 : Nat := 2962405968161475457855139

theorem tailTrace_5769265 : CollatzResearch.WordTrace tailWord_5769265 prefixEnd_5769265 2962405968161475457855139 := by
  unfold tailWord_5769265
  simp only [CollatzResearch.WordTrace]
  refine ⟨210422381443945691862413249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140281587629297127908275499 210422381443945691862413249)
  ·
    refine ⟨157816786082959268896809937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210422381443945691862413249 157816786082959268896809937)
    ·
      refine ⟨118362589562219451672607453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157816786082959268896809937 118362589562219451672607453)
      ·
        refine ⟨44385971085832294377227795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118362589562219451672607453 44385971085832294377227795)
        ·
          refine ⟨66578956628748441565841693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44385971085832294377227795 66578956628748441565841693)
          ·
            refine ⟨24967108735780665587190635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66578956628748441565841693 24967108735780665587190635)
            ·
              refine ⟨37450663103670998380785953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24967108735780665587190635 37450663103670998380785953)
              ·
                refine ⟨28087997327753248785589465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37450663103670998380785953 28087997327753248785589465)
                ·
                  refine ⟨21065997995814936589192099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28087997327753248785589465 21065997995814936589192099)
                  ·
                    refine ⟨31598996993722404883788149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21065997995814936589192099 31598996993722404883788149)
                    ·
                      refine ⟨2962405968161475457855139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31598996993722404883788149 2962405968161475457855139)
                      ·
                        rfl

theorem cell23_5769265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_5769265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769265 prefixEnd_5769265 := by exact prefixLift 5769265
  have htrace : WordTrace (prefixWord ++ tailWord_5769265) baseStart_5769265 baseEnd_5769265 := by
    simpa [prefixWord, tailWord_5769265, baseEnd_5769265] using wordTrace_append hprefix tailTrace_5769265
  have hstable : (prefixWord ++ tailWord_5769265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769265).length < 2 ^ (prefixWord ++ tailWord_5769265).sum := by decide
  have hdescent : baseEnd_5769265 < baseStart_5769265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769266 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_5769266 : Nat := 118140960795 + 5769266 * 2 ^ 59
def prefixEnd_5769266 : Nat := 4983230072969 + 3 ^ 40 * 5769266 * 2
def baseEnd_5769266 : Nat := 2962406481642129953942635

theorem tailTrace_5769266 : CollatzResearch.WordTrace tailWord_5769266 prefixEnd_5769266 2962406481642129953942635 := by
  unfold tailWord_5769266
  simp only [CollatzResearch.WordTrace]
  refine ⟨52605604479235517258299913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140281611944628046022133101 52605604479235517258299913)
  ·
    refine ⟨39454203359426637943724935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52605604479235517258299913 39454203359426637943724935)
    ·
      refine ⟨59181305039139956915587403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39454203359426637943724935 59181305039139956915587403)
      ·
        refine ⟨88771957558709935373381105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59181305039139956915587403 88771957558709935373381105)
        ·
          refine ⟨66578968169032451530035829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88771957558709935373381105 66578968169032451530035829)
          ·
            refine ⟨6241778265846792330940859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66578968169032451530035829 6241778265846792330940859)
            ·
              refine ⟨9362667398770188496411289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6241778265846792330940859 9362667398770188496411289)
              ·
                refine ⟨7022000549077641372308467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9362667398770188496411289 7022000549077641372308467)
                ·
                  refine ⟨10533000823616462058462701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7022000549077641372308467 10533000823616462058462701)
                  ·
                    refine ⟨3949875308856173271923513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10533000823616462058462701 3949875308856173271923513)
                    ·
                      refine ⟨2962406481642129953942635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3949875308856173271923513 2962406481642129953942635)
                      ·
                        rfl

theorem cell23_5769266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_5769266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769266 prefixEnd_5769266 := by exact prefixLift 5769266
  have htrace : WordTrace (prefixWord ++ tailWord_5769266) baseStart_5769266 baseEnd_5769266 := by
    simpa [prefixWord, tailWord_5769266, baseEnd_5769266] using wordTrace_append hprefix tailTrace_5769266
  have hstable : (prefixWord ++ tailWord_5769266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769266).length < 2 ^ (prefixWord ++ tailWord_5769266).sum := by decide
  have hdescent : baseEnd_5769266 < baseStart_5769266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769295 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 3]
def baseStart_5769295 : Nat := 118140960795 + 5769295 * 2 ^ 59
def prefixEnd_5769295 : Nat := 4983230072969 + 3 ^ 40 * 5769295 * 2
def baseEnd_5769295 : Nat := 2962421372581110340480001

theorem tailTrace_5769295 : CollatzResearch.WordTrace tailWord_5769295 prefixEnd_5769295 2962421372581110340480001 := by
  unfold tailWord_5769295
  simp only [CollatzResearch.WordTrace]
  refine ⟨210423475633837006986005339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140282317089224671324003559 210423475633837006986005339)
  ·
    refine ⟨315635213450755510479008009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210423475633837006986005339 315635213450755510479008009)
    ·
      refine ⟨236726410088066632859256007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315635213450755510479008009 236726410088066632859256007)
      ·
        refine ⟨355089615132099949288884011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236726410088066632859256007 355089615132099949288884011)
        ·
          refine ⟨532634422698149923933326017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355089615132099949288884011 532634422698149923933326017)
          ·
            refine ⟨399475817023612442949994513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532634422698149923933326017 399475817023612442949994513)
            ·
              refine ⟨299606862767709332212495885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399475817023612442949994513 299606862767709332212495885)
              ·
                refine ⟨112352573537890999579685957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299606862767709332212495885 112352573537890999579685957)
                ·
                  refine ⟨21066107538354562421191117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112352573537890999579685957 21066107538354562421191117)
                  ·
                    refine ⟨7899790326882960907946669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21066107538354562421191117 7899790326882960907946669)
                    ·
                      refine ⟨2962421372581110340480001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7899790326882960907946669 2962421372581110340480001)
                      ·
                        rfl

theorem cell23_5769295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_5769295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769295 prefixEnd_5769295 := by exact prefixLift 5769295
  have htrace : WordTrace (prefixWord ++ tailWord_5769295) baseStart_5769295 baseEnd_5769295 := by
    simpa [prefixWord, tailWord_5769295, baseEnd_5769295] using wordTrace_append hprefix tailTrace_5769295
  have hstable : (prefixWord ++ tailWord_5769295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769295).length < 2 ^ (prefixWord ++ tailWord_5769295).sum := by decide
  have hdescent : baseEnd_5769295 < baseStart_5769295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769309 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5769309 : Nat := 118140960795 + 5769309 * 2 ^ 59
def prefixEnd_5769309 : Nat := 4983230072969 + 3 ^ 40 * 5769309 * 2
def baseEnd_5769309 : Nat := 2962428561310273285704937

theorem tailTrace_5769309 : CollatzResearch.WordTrace tailWord_5769309 prefixEnd_5769309 2962428561310273285704937 := by
  unfold tailWord_5769309
  simp only [CollatzResearch.WordTrace]
  refine ⟨210423986255786287377014981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140282657503857524918009987 210423986255786287377014981)
  ·
    refine ⟨39454497422959928883190309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210423986255786287377014981 39454497422959928883190309)
    ·
      refine ⟨7397718266804986665598183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39454497422959928883190309 7397718266804986665598183)
      ·
        refine ⟨11096577400207479998397275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7397718266804986665598183 11096577400207479998397275)
        ·
          refine ⟨16644866100311219997595913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11096577400207479998397275 16644866100311219997595913)
          ·
            refine ⟨12483649575233414998196935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16644866100311219997595913 12483649575233414998196935)
            ·
              refine ⟨18725474362850122497295403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12483649575233414998196935 18725474362850122497295403)
              ·
                refine ⟨28088211544275183745943105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18725474362850122497295403 28088211544275183745943105)
                ·
                  refine ⟨21066158658206387809457329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28088211544275183745943105 21066158658206387809457329)
                  ·
                    refine ⟨15799618993654790857092997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21066158658206387809457329 15799618993654790857092997)
                    ·
                      refine ⟨2962428561310273285704937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15799618993654790857092997 2962428561310273285704937)
                      ·
                        rfl

theorem cell23_5769309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5769309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769309 prefixEnd_5769309 := by exact prefixLift 5769309
  have htrace : WordTrace (prefixWord ++ tailWord_5769309) baseStart_5769309 baseEnd_5769309 := by
    simpa [prefixWord, tailWord_5769309, baseEnd_5769309] using wordTrace_append hprefix tailTrace_5769309
  have hstable : (prefixWord ++ tailWord_5769309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769309).length < 2 ^ (prefixWord ++ tailWord_5769309).sum := by decide
  have hdescent : baseEnd_5769309 < baseStart_5769309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769312 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 3]
def baseStart_5769312 : Nat := 118140960795 + 5769312 * 2 ^ 59
def prefixEnd_5769312 : Nat := 4983230072969 + 3 ^ 40 * 5769312 * 2
def baseEnd_5769312 : Nat := 2962430101752236773967423

theorem tailTrace_5769312 : CollatzResearch.WordTrace tailWord_5769312 prefixEnd_5769312 2962430101752236773967423 := by
  unfold tailWord_5769312
  simp only [CollatzResearch.WordTrace]
  refine ⟨105212047837387709444687095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140282730449850279259582793 105212047837387709444687095)
  ·
    refine ⟨157818071756081564167030643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105212047837387709444687095 157818071756081564167030643)
    ·
      refine ⟨236727107634122346250545965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157818071756081564167030643 236727107634122346250545965)
      ·
        refine ⟨88772665362795879843954737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236727107634122346250545965 88772665362795879843954737)
        ·
          refine ⟨66579499022096909882966053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88772665362795879843954737 66579499022096909882966053)
          ·
            refine ⟨12483656066643170603056135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66579499022096909882966053 12483656066643170603056135)
            ·
              refine ⟨18725484099964755904584203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12483656066643170603056135 18725484099964755904584203)
              ·
                refine ⟨28088226149947133856876305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18725484099964755904584203 28088226149947133856876305)
                ·
                  refine ⟨21066169612460350392657229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28088226149947133856876305 21066169612460350392657229)
                  ·
                    refine ⟨7899813604672631397246461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21066169612460350392657229 7899813604672631397246461)
                    ·
                      refine ⟨2962430101752236773967423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7899813604672631397246461 2962430101752236773967423)
                      ·
                        rfl

theorem cell23_5769312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_5769312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769312 prefixEnd_5769312 := by exact prefixLift 5769312
  have htrace : WordTrace (prefixWord ++ tailWord_5769312) baseStart_5769312 baseEnd_5769312 := by
    simpa [prefixWord, tailWord_5769312, baseEnd_5769312] using wordTrace_append hprefix tailTrace_5769312
  have hstable : (prefixWord ++ tailWord_5769312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769312).length < 2 ^ (prefixWord ++ tailWord_5769312).sum := by decide
  have hdescent : baseEnd_5769312 < baseStart_5769312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769315 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 4, 5]
def baseStart_5769315 : Nat := 118140960795 + 5769315 * 2 ^ 59
def prefixEnd_5769315 : Nat := 4983230072969 + 3 ^ 40 * 5769315 * 2
def baseEnd_5769315 : Nat := 987477214064733420743303

theorem tailTrace_5769315 : CollatzResearch.WordTrace tailWord_5769315 prefixEnd_5769315 987477214064733420743303 := by
  unfold tailWord_5769315
  simp only [CollatzResearch.WordTrace]
  refine ⟨210424205093764550401733399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140282803395843033601155599 210424205093764550401733399)
  ·
    refine ⟨315636307640646825602600099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210424205093764550401733399 315636307640646825602600099)
    ·
      refine ⟨473454461460970238403900149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315636307640646825602600099 473454461460970238403900149)
      ·
        refine ⟨44386355761965959850365639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 473454461460970238403900149 44386355761965959850365639)
        ·
          refine ⟨66579533642948939775548459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44386355761965959850365639 66579533642948939775548459)
          ·
            refine ⟨99869300464423409663322689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66579533642948939775548459 99869300464423409663322689)
            ·
              refine ⟨74901975348317557247492017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99869300464423409663322689 74901975348317557247492017)
              ·
                refine ⟨56176481511238167935619013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74901975348317557247492017 56176481511238167935619013)
                ·
                  refine ⟨10533090283357156487928565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56176481511238167935619013 10533090283357156487928565)
                  ·
                    refine ⟨987477214064733420743303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10533090283357156487928565 987477214064733420743303)
                    ·
                      rfl

theorem cell23_5769315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 5].length) (baseStart_5769315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769315 prefixEnd_5769315 := by exact prefixLift 5769315
  have htrace : WordTrace (prefixWord ++ tailWord_5769315) baseStart_5769315 baseEnd_5769315 := by
    simpa [prefixWord, tailWord_5769315, baseEnd_5769315] using wordTrace_append hprefix tailTrace_5769315
  have hstable : (prefixWord ++ tailWord_5769315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769315).length < 2 ^ (prefixWord ++ tailWord_5769315).sum := by decide
  have hdescent : baseEnd_5769315 < baseStart_5769315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769365 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_5769365 : Nat := 118140960795 + 5769365 * 2 ^ 59
def prefixEnd_5769365 : Nat := 4983230072969 + 3 ^ 40 * 5769365 * 2
def baseEnd_5769365 : Nat := 2962457316226925066604679

theorem tailTrace_5769365 : CollatzResearch.WordTrace tailWord_5769365 prefixEnd_5769365 2962457316226925066604679 := by
  unfold tailWord_5769365
  simp only [CollatzResearch.WordTrace]
  refine ⟨210426028743583408941053549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140284019162388939294035699 210426028743583408941053549)
  ·
    refine ⟨78909760778843778352895081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210426028743583408941053549 78909760778843778352895081)
    ·
      refine ⟨59182320584132833764671311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78909760778843778352895081 59182320584132833764671311)
      ·
        refine ⟨88773480876199250647006967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59182320584132833764671311 88773480876199250647006967)
        ·
          refine ⟨133160221314298875970510451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88773480876199250647006967 133160221314298875970510451)
          ·
            refine ⟨199740331971448313955765677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133160221314298875970510451 199740331971448313955765677)
            ·
              refine ⟨74902624489293117733412129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199740331971448313955765677 74902624489293117733412129)
              ·
                refine ⟨56176968366969838300059097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74902624489293117733412129 56176968366969838300059097)
                ·
                  refine ⟨42132726275227378725044323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56176968366969838300059097 42132726275227378725044323)
                  ·
                    refine ⟨63199089412841068087566485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42132726275227378725044323 63199089412841068087566485)
                    ·
                      refine ⟨2962457316226925066604679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63199089412841068087566485 2962457316226925066604679)
                      ·
                        rfl

theorem cell23_5769365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_5769365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769365 prefixEnd_5769365 := by exact prefixLift 5769365
  have htrace : WordTrace (prefixWord ++ tailWord_5769365) baseStart_5769365 baseEnd_5769365 := by
    simpa [prefixWord, tailWord_5769365, baseEnd_5769365] using wordTrace_append hprefix tailTrace_5769365
  have hstable : (prefixWord ++ tailWord_5769365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769365).length < 2 ^ (prefixWord ++ tailWord_5769365).sum := by decide
  have hdescent : baseEnd_5769365 < baseStart_5769365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769372 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_5769372 : Nat := 118140960795 + 5769372 * 2 ^ 59
def prefixEnd_5769372 : Nat := 4983230072969 + 3 ^ 40 * 5769372 * 2
def baseEnd_5769372 : Nat := 2962460910591506539217147

theorem tailTrace_5769372 : CollatzResearch.WordTrace tailWord_5769372 prefixEnd_5769372 2962460910591506539217147 := by
  unfold tailWord_5769372
  simp only [CollatzResearch.WordTrace]
  refine ⟨105213142027279024568279185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140284189369705366091038913 105213142027279024568279185)
  ·
    refine ⟨78909856520459268426209389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105213142027279024568279185 78909856520459268426209389)
    ·
      refine ⟨29591196195172225659828521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78909856520459268426209389 29591196195172225659828521)
      ·
        refine ⟨22193397146379169244871391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29591196195172225659828521 22193397146379169244871391)
        ·
          refine ⟨33290095719568753867307087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22193397146379169244871391 33290095719568753867307087)
          ·
            refine ⟨49935143579353130800960631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33290095719568753867307087 49935143579353130800960631)
            ·
              refine ⟨74902715369029696201440947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49935143579353130800960631 74902715369029696201440947)
              ·
                refine ⟨112354073053544544302161421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74902715369029696201440947 112354073053544544302161421)
                ·
                  refine ⟨42132777395079204113310533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112354073053544544302161421 42132777395079204113310533)
                  ·
                    refine ⟨7899895761577350771245725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42132777395079204113310533 7899895761577350771245725)
                    ·
                      refine ⟨2962460910591506539217147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7899895761577350771245725 2962460910591506539217147)
                      ·
                        rfl

theorem cell23_5769372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_5769372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769372 prefixEnd_5769372 := by exact prefixLift 5769372
  have htrace : WordTrace (prefixWord ++ tailWord_5769372) baseStart_5769372 baseEnd_5769372 := by
    simpa [prefixWord, tailWord_5769372, baseEnd_5769372] using wordTrace_append hprefix tailTrace_5769372
  have hstable : (prefixWord ++ tailWord_5769372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769372).length < 2 ^ (prefixWord ++ tailWord_5769372).sum := by decide
  have hdescent : baseEnd_5769372 < baseStart_5769372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769389 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_5769389 : Nat := 118140960795 + 5769389 * 2 ^ 59
def prefixEnd_5769389 : Nat := 4983230072969 + 3 ^ 40 * 5769389 * 2
def baseEnd_5769389 : Nat := 2962469639762632972704569

theorem tailTrace_5769389 : CollatzResearch.WordTrace tailWord_5769389 prefixEnd_5769389 2962469639762632972704569 := by
  unfold tailWord_5769389
  simp only [CollatzResearch.WordTrace]
  refine ⟨210426904095496461039927221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140284602730330974026618147 210426904095496461039927221)
  ·
    refine ⟨19727522258952793222493177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210426904095496461039927221 19727522258952793222493177)
    ·
      refine ⟨14795641694214594916869883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19727522258952793222493177 14795641694214594916869883)
      ·
        refine ⟨22193462541321892375304825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14795641694214594916869883 22193462541321892375304825)
        ·
          refine ⟨16645096905991419281478619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22193462541321892375304825 16645096905991419281478619)
          ·
            refine ⟨24967645358987128922217929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16645096905991419281478619 24967645358987128922217929)
            ·
              refine ⟨18725734019240346691663447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24967645358987128922217929 18725734019240346691663447)
              ·
                refine ⟨28088601028860520037495171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18725734019240346691663447 28088601028860520037495171)
                ·
                  refine ⟨42132901543290780056242757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28088601028860520037495171 42132901543290780056242757)
                  ·
                    refine ⟨7899919039367021260545517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42132901543290780056242757 7899919039367021260545517)
                    ·
                      refine ⟨2962469639762632972704569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7899919039367021260545517 2962469639762632972704569)
                      ·
                        rfl

theorem cell23_5769389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_5769389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769389 prefixEnd_5769389 := by exact prefixLift 5769389
  have htrace : WordTrace (prefixWord ++ tailWord_5769389) baseStart_5769389 baseEnd_5769389 := by
    simpa [prefixWord, tailWord_5769389, baseEnd_5769389] using wordTrace_append hprefix tailTrace_5769389
  have hstable : (prefixWord ++ tailWord_5769389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769389).length < 2 ^ (prefixWord ++ tailWord_5769389).sum := by decide
  have hdescent : baseEnd_5769389 < baseStart_5769389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769406 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_5769406 : Nat := 118140960795 + 5769406 * 2 ^ 59
def prefixEnd_5769406 : Nat := 4983230072969 + 3 ^ 40 * 5769406 * 2
def baseEnd_5769406 : Nat := 2962478368933759406191991

theorem tailTrace_5769406 : CollatzResearch.WordTrace tailWord_5769406 prefixEnd_5769406 2962478368933759406191991 := by
  unfold tailWord_5769406
  simp only [CollatzResearch.WordTrace]
  refine ⟨26303440517054359117912009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140285016090956581962197381 26303440517054359117912009)
  ·
    refine ⟨19727580387790769338434007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26303440517054359117912009 19727580387790769338434007)
    ·
      refine ⟨29591370581686154007651011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19727580387790769338434007 29591370581686154007651011)
      ·
        refine ⟨44387055872529231011476517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29591370581686154007651011 44387055872529231011476517)
        ·
          refine ⟨8322572976099230814651847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44387055872529231011476517 8322572976099230814651847)
          ·
            refine ⟨12483859464148846221977771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8322572976099230814651847 12483859464148846221977771)
            ·
              refine ⟨18725789196223269332966657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12483859464148846221977771 18725789196223269332966657)
              ·
                refine ⟨14044341897167451999724993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18725789196223269332966657 14044341897167451999724993)
                ·
                  refine ⟨10533256422875588999793745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14044341897167451999724993 10533256422875588999793745)
                  ·
                    refine ⟨7899942317156691749845309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10533256422875588999793745 7899942317156691749845309)
                    ·
                      refine ⟨2962478368933759406191991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7899942317156691749845309 2962478368933759406191991)
                      ·
                        rfl

theorem cell23_5769406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_5769406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769406 prefixEnd_5769406 := by exact prefixLift 5769406
  have htrace : WordTrace (prefixWord ++ tailWord_5769406) baseStart_5769406 baseEnd_5769406 := by
    simpa [prefixWord, tailWord_5769406, baseEnd_5769406] using wordTrace_append hprefix tailTrace_5769406
  have hstable : (prefixWord ++ tailWord_5769406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769406).length < 2 ^ (prefixWord ++ tailWord_5769406).sum := by decide
  have hdescent : baseEnd_5769406 < baseStart_5769406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769415 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_5769415 : Nat := 118140960795 + 5769415 * 2 ^ 59
def prefixEnd_5769415 : Nat := 4983230072969 + 3 ^ 40 * 5769415 * 2
def baseEnd_5769415 : Nat := 2962482990259649870979449

theorem tailTrace_5769415 : CollatzResearch.WordTrace tailWord_5769415 prefixEnd_5769415 2962482990259649870979449 := by
  unfold tailWord_5769415
  simp only [CollatzResearch.WordTrace]
  refine ⟨210427852393402267480373699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140285234928934844986915799 210427852393402267480373699)
  ·
    refine ⟨315641778590103401220560549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210427852393402267480373699 315641778590103401220560549)
    ·
      refine ⟨59182833485644387728855103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315641778590103401220560549 59182833485644387728855103)
      ·
        refine ⟨88774250228466581593282655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59182833485644387728855103 88774250228466581593282655)
        ·
          refine ⟨133161375342699872389923983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88774250228466581593282655 133161375342699872389923983)
          ·
            refine ⟨199742063014049808584885975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133161375342699872389923983 199742063014049808584885975)
            ·
              refine ⟨299613094521074712877328963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199742063014049808584885975 299613094521074712877328963)
              ·
                refine ⟨449419641781612069315993445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299613094521074712877328963 449419641781612069315993445)
                ·
                  refine ⟨84266182834052262996748771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449419641781612069315993445 84266182834052262996748771)
                  ·
                    refine ⟨126399274251078394495123157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84266182834052262996748771 126399274251078394495123157)
                    ·
                      refine ⟨2962482990259649870979449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126399274251078394495123157 2962482990259649870979449)
                      ·
                        rfl

theorem cell23_5769415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_5769415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769415 prefixEnd_5769415 := by exact prefixLift 5769415
  have htrace : WordTrace (prefixWord ++ tailWord_5769415) baseStart_5769415 baseEnd_5769415 := by
    simpa [prefixWord, tailWord_5769415, baseEnd_5769415] using wordTrace_append hprefix tailTrace_5769415
  have hstable : (prefixWord ++ tailWord_5769415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769415).length < 2 ^ (prefixWord ++ tailWord_5769415).sum := by decide
  have hdescent : baseEnd_5769415 < baseStart_5769415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769426 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 6]
def baseStart_5769426 : Nat := 118140960795 + 5769426 * 2 ^ 59
def prefixEnd_5769426 : Nat := 4983230072969 + 3 ^ 40 * 5769426 * 2
def baseEnd_5769426 : Nat := 329165404282983258660211

theorem tailTrace_5769426 : CollatzResearch.WordTrace tailWord_5769426 prefixEnd_5769426 329165404282983258660211 := by
  unfold tailWord_5769426
  simp only [CollatzResearch.WordTrace]
  refine ⟨52607063399090604089756033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140285502397574944239349421 52607063399090604089756033)
  ·
    refine ⟨39455297549317953067317025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52607063399090604089756033 39455297549317953067317025)
    ·
      refine ⟨29591473161988464800487769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39455297549317953067317025 29591473161988464800487769)
      ·
        refine ⟨22193604871491348600365827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29591473161988464800487769 22193604871491348600365827)
        ·
          refine ⟨33290407307237022900548741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22193604871491348600365827 33290407307237022900548741)
          ·
            refine ⟨6241951370106941793852889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33290407307237022900548741 6241951370106941793852889)
            ·
              refine ⟨4681463527580206345389667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6241951370106941793852889 4681463527580206345389667)
              ·
                refine ⟨7022195291370309518084501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4681463527580206345389667 7022195291370309518084501)
                ·
                  refine ⟨329165404282983258660211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7022195291370309518084501 329165404282983258660211)
                  ·
                    rfl

theorem cell23_5769426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_5769426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769426 prefixEnd_5769426 := by exact prefixLift 5769426
  have htrace : WordTrace (prefixWord ++ tailWord_5769426) baseStart_5769426 baseEnd_5769426 := by
    simpa [prefixWord, tailWord_5769426, baseEnd_5769426] using wordTrace_append hprefix tailTrace_5769426
  have hstable : (prefixWord ++ tailWord_5769426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769426).length < 2 ^ (prefixWord ++ tailWord_5769426).sum := by decide
  have hdescent : baseEnd_5769426 < baseStart_5769426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769452 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_5769452 : Nat := 118140960795 + 5769452 * 2 ^ 59
def prefixEnd_5769452 : Nat := 4983230072969 + 3 ^ 40 * 5769452 * 2
def baseEnd_5769452 : Nat := 987500663014622075405593

theorem tailTrace_5769452 : CollatzResearch.WordTrace tailWord_5769452 prefixEnd_5769452 987500663014622075405593 := by
  unfold tailWord_5769452
  simp only [CollatzResearch.WordTrace]
  refine ⟨105214600947134111399735305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140286134596178815199647073 105214600947134111399735305)
  ·
    refine ⟨78910950710350583549801479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105214600947134111399735305 78910950710350583549801479)
    ·
      refine ⟨118366426065525875324702219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78910950710350583549801479 118366426065525875324702219)
      ·
        refine ⟨177549639098288812987053329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118366426065525875324702219 177549639098288812987053329)
        ·
          refine ⟨133162229323716609740289997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177549639098288812987053329 133162229323716609740289997)
          ·
            refine ⟨49935835996393728652608749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133162229323716609740289997 49935835996393728652608749)
            ·
              refine ⟨18725938498647648244728281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49935835996393728652608749 18725938498647648244728281)
              ·
                refine ⟨14044453873985736183546211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18725938498647648244728281 14044453873985736183546211)
                ·
                  refine ⟨21066680810978604275319317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14044453873985736183546211 21066680810978604275319317)
                  ·
                    refine ⟨987500663014622075405593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21066680810978604275319317 987500663014622075405593)
                    ·
                      rfl

theorem cell23_5769452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_5769452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769452 prefixEnd_5769452 := by exact prefixLift 5769452
  have htrace : WordTrace (prefixWord ++ tailWord_5769452) baseStart_5769452 baseEnd_5769452 := by
    simpa [prefixWord, tailWord_5769452, baseEnd_5769452] using wordTrace_append hprefix tailTrace_5769452
  have hstable : (prefixWord ++ tailWord_5769452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769452).length < 2 ^ (prefixWord ++ tailWord_5769452).sum := by decide
  have hdescent : baseEnd_5769452 < baseStart_5769452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769482 : List Nat := [3, 1, 2, 2, 1, 1, 5, 8]
def baseStart_5769482 : Nat := 118140960795 + 5769482 * 2 ^ 59
def prefixEnd_5769482 : Nat := 4983230072969 + 3 ^ 40 * 5769482 * 2
def baseEnd_5769482 : Nat := 109722866424574115142283

theorem tailTrace_5769482 : CollatzResearch.WordTrace tailWord_5769482 prefixEnd_5769482 109722866424574115142283 := by
  unfold tailWord_5769482
  simp only [CollatzResearch.WordTrace]
  refine ⟨52607574021039884480765675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140286864056106358615375133 52607574021039884480765675)
  ·
    refine ⟨78911361031559826721148513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52607574021039884480765675 78911361031559826721148513)
    ·
      refine ⟨59183520773669870040861385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78911361031559826721148513 59183520773669870040861385)
      ·
        refine ⟨44387640580252402530646039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59183520773669870040861385 44387640580252402530646039)
        ·
          refine ⟨66581460870378603795969059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44387640580252402530646039 66581460870378603795969059)
          ·
            refine ⟨99872191305567905693953589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66581460870378603795969059 99872191305567905693953589)
            ·
              refine ⟨9363017934896991158808149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99872191305567905693953589 9363017934896991158808149)
              ·
                refine ⟨109722866424574115142283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9363017934896991158808149 109722866424574115142283)
                ·
                  rfl

theorem cell23_5769482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_5769482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769482 prefixEnd_5769482 := by exact prefixLift 5769482
  have htrace : WordTrace (prefixWord ++ tailWord_5769482) baseStart_5769482 baseEnd_5769482 := by
    simpa [prefixWord, tailWord_5769482, baseEnd_5769482] using wordTrace_append hprefix tailTrace_5769482
  have hstable : (prefixWord ++ tailWord_5769482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769482).length < 2 ^ (prefixWord ++ tailWord_5769482).sum := by decide
  have hdescent : baseEnd_5769482 < baseStart_5769482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769489 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_5769489 : Nat := 118140960795 + 5769489 * 2 ^ 59
def prefixEnd_5769489 : Nat := 4983230072969 + 3 ^ 40 * 5769489 * 2
def baseEnd_5769489 : Nat := 2962520987828082581454109

theorem tailTrace_5769489 : CollatzResearch.WordTrace tailWord_5769489 prefixEnd_5769489 2962520987828082581454109 := by
  unfold tailWord_5769489
  simp only [CollatzResearch.WordTrace]
  refine ⟨210430551395134178118567521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140287034263422785412378347 210430551395134178118567521)
  ·
    refine ⟨157822913546350633588925641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210430551395134178118567521 157822913546350633588925641)
    ·
      refine ⟨118367185159762975191694231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157822913546350633588925641 118367185159762975191694231)
      ·
        refine ⟨177550777739644462787541347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118367185159762975191694231 177550777739644462787541347)
        ·
          refine ⟨266326166609466694181312021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177550777739644462787541347 266326166609466694181312021)
          ·
            refine ⟨12484039059818751289749001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 266326166609466694181312021 12484039059818751289749001)
            ·
              refine ⟨9363029294864063467311751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12484039059818751289749001 9363029294864063467311751)
              ·
                refine ⟨14044543942296095200967627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9363029294864063467311751 14044543942296095200967627)
                ·
                  refine ⟨21066815913444142801451441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14044543942296095200967627 21066815913444142801451441)
                  ·
                    refine ⟨15800111935083107101088581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21066815913444142801451441 15800111935083107101088581)
                    ·
                      refine ⟨2962520987828082581454109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15800111935083107101088581 2962520987828082581454109)
                      ·
                        rfl

theorem cell23_5769489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_5769489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769489 prefixEnd_5769489 := by exact prefixLift 5769489
  have htrace : WordTrace (prefixWord ++ tailWord_5769489) baseStart_5769489 baseEnd_5769489 := by
    simpa [prefixWord, tailWord_5769489, baseEnd_5769489] using wordTrace_append hprefix tailTrace_5769489
  have hstable : (prefixWord ++ tailWord_5769489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769489).length < 2 ^ (prefixWord ++ tailWord_5769489).sum := by decide
  have hdescent : baseEnd_5769489 < baseStart_5769489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769540 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5769540 : Nat := 118140960795 + 5769540 * 2 ^ 59
def prefixEnd_5769540 : Nat := 4983230072969 + 3 ^ 40 * 5769540 * 2
def baseEnd_5769540 : Nat := 2962547175341461881916375

theorem tailTrace_5769540 : CollatzResearch.WordTrace tailWord_5769540 prefixEnd_5769540 2962547175341461881916375 := by
  unfold tailWord_5769540
  simp only [CollatzResearch.WordTrace]
  refine ⟨105216205758974706914337037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140288274345299609219116049 105216205758974706914337037)
  ·
    refine ⟨39456077159615515092876389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105216205758974706914337037 39456077159615515092876389)
    ·
      refine ⟨7398014467427909079914323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39456077159615515092876389 7398014467427909079914323)
      ·
        refine ⟨11097021701141863619871485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7398014467427909079914323 11097021701141863619871485)
        ·
          refine ⟨4161383137928198857451807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11097021701141863619871485 4161383137928198857451807)
          ·
            refine ⟨6242074706892298286177711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161383137928198857451807 6242074706892298286177711)
            ·
              refine ⟨9363112060338447429266567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6242074706892298286177711 9363112060338447429266567)
              ·
                refine ⟨14044668090507671143899851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9363112060338447429266567 14044668090507671143899851)
                ·
                  refine ⟨21067002135761506715849777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14044668090507671143899851 21067002135761506715849777)
                  ·
                    refine ⟨15800251601821130036887333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21067002135761506715849777 15800251601821130036887333)
                    ·
                      refine ⟨2962547175341461881916375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15800251601821130036887333 2962547175341461881916375)
                      ·
                        rfl

theorem cell23_5769540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5769540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769540 prefixEnd_5769540 := by exact prefixLift 5769540
  have htrace : WordTrace (prefixWord ++ tailWord_5769540) baseStart_5769540 baseEnd_5769540 := by
    simpa [prefixWord, tailWord_5769540, baseEnd_5769540] using wordTrace_append hprefix tailTrace_5769540
  have hstable : (prefixWord ++ tailWord_5769540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769540).length < 2 ^ (prefixWord ++ tailWord_5769540).sum := by decide
  have hdescent : baseEnd_5769540 < baseStart_5769540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769543 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_5769543 : Nat := 118140960795 + 5769543 * 2 ^ 59
def prefixEnd_5769543 : Nat := 4983230072969 + 3 ^ 40 * 5769543 * 2
def baseEnd_5769543 : Nat := 2962548715783425370178861

theorem tailTrace_5769543 : CollatzResearch.WordTrace tailWord_5769543 prefixEnd_5769543 2962548715783425370178861 := by
  unfold tailWord_5769543
  simp only [CollatzResearch.WordTrace]
  refine ⟨210432520936938545341033283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140288347291292363560688855 210432520936938545341033283)
  ·
    refine ⟨315648781405407818011549925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210432520936938545341033283 315648781405407818011549925)
    ·
      refine ⟨59184146513513965877165611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315648781405407818011549925 59184146513513965877165611)
      ·
        refine ⟨88776219770270948815748417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59184146513513965877165611 88776219770270948815748417)
        ·
          refine ⟨66582164827703211611811313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88776219770270948815748417 66582164827703211611811313)
          ·
            refine ⟨49936623620777408708858485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66582164827703211611811313 49936623620777408708858485)
            ·
              refine ⟨4681558464447882066455483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49936623620777408708858485 4681558464447882066455483)
              ·
                refine ⟨7022337696671823099683225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4681558464447882066455483 7022337696671823099683225)
                ·
                  refine ⟨5266753272503867324762419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7022337696671823099683225 5266753272503867324762419)
                  ·
                    refine ⟨7900129908755800987143629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5266753272503867324762419 7900129908755800987143629)
                    ·
                      refine ⟨2962548715783425370178861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7900129908755800987143629 2962548715783425370178861)
                      ·
                        rfl

theorem cell23_5769543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_5769543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769543 prefixEnd_5769543 := by exact prefixLift 5769543
  have htrace : WordTrace (prefixWord ++ tailWord_5769543) baseStart_5769543 baseEnd_5769543 := by
    simpa [prefixWord, tailWord_5769543, baseEnd_5769543] using wordTrace_append hprefix tailTrace_5769543
  have hstable : (prefixWord ++ tailWord_5769543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769543).length < 2 ^ (prefixWord ++ tailWord_5769543).sum := by decide
  have hdescent : baseEnd_5769543 < baseStart_5769543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769553 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 1, 3, 2]
def baseStart_5769553 : Nat := 118140960795 + 5769553 * 2 ^ 59
def prefixEnd_5769553 : Nat := 4983230072969 + 3 ^ 40 * 5769553 * 2
def baseEnd_5769553 : Nat := 2962553850589970331053815

theorem tailTrace_5769553 : CollatzResearch.WordTrace tailWord_5769553 prefixEnd_5769553 2962553850589970331053815 := by
  unfold tailWord_5769553
  simp only [CollatzResearch.WordTrace]
  refine ⟨210432885666902317048897313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140288590444601544699264875 210432885666902317048897313)
  ·
    refine ⟨157824664250176737786672985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210432885666902317048897313 157824664250176737786672985)
    ·
      refine ⟨118368498187632553340004739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157824664250176737786672985 118368498187632553340004739)
      ·
        refine ⟨177552747281448830010007109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118368498187632553340004739 177552747281448830010007109)
        ·
          refine ⟨33291140115271655626876333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177552747281448830010007109 33291140115271655626876333)
          ·
            refine ⟨12484177543226870860078625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33291140115271655626876333 12484177543226870860078625)
            ·
              refine ⟨9363133157420153145058969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12484177543226870860078625 9363133157420153145058969)
              ·
                refine ⟨7022349868065114858794227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9363133157420153145058969 7022349868065114858794227)
                ·
                  refine ⟨10533524802097672288191341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7022349868065114858794227 10533524802097672288191341)
                  ·
                    refine ⟨3950071800786627108071753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10533524802097672288191341 3950071800786627108071753)
                    ·
                      refine ⟨2962553850589970331053815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3950071800786627108071753 2962553850589970331053815)
                      ·
                        rfl

theorem cell23_5769553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_5769553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769553 prefixEnd_5769553 := by exact prefixLift 5769553
  have htrace : WordTrace (prefixWord ++ tailWord_5769553) baseStart_5769553 baseEnd_5769553 := by
    simpa [prefixWord, tailWord_5769553, baseEnd_5769553] using wordTrace_append hprefix tailTrace_5769553
  have hstable : (prefixWord ++ tailWord_5769553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769553).length < 2 ^ (prefixWord ++ tailWord_5769553).sum := by decide
  have hdescent : baseEnd_5769553 < baseStart_5769553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769640 : List Nat := [2, 1, 6, 1, 1, 1, 4, 2, 5]
def baseStart_5769640 : Nat := 118140960795 + 5769640 * 2 ^ 59
def prefixEnd_5769640 : Nat := 4983230072969 + 3 ^ 40 * 5769640 * 2
def baseEnd_5769640 : Nat := 329177613711879054518435

theorem tailTrace_5769640 : CollatzResearch.WordTrace tailWord_5769640 prefixEnd_5769640 329177613711879054518435 := by
  unfold tailWord_5769640
  simp only [CollatzResearch.WordTrace]
  refine ⟨105218029408793565453657187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140290705878391420604876249 105218029408793565453657187)
  ·
    refine ⟨157827044113190348180485781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105218029408793565453657187 157827044113190348180485781)
    ·
      refine ⟨7398142692805797570960271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157827044113190348180485781 7398142692805797570960271)
      ·
        refine ⟨11097214039208696356440407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7398142692805797570960271 11097214039208696356440407)
        ·
          refine ⟨16645821058813044534660611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11097214039208696356440407 16645821058813044534660611)
          ·
            refine ⟨24968731588219566801990917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16645821058813044534660611 24968731588219566801990917)
            ·
              refine ⟨4681637172791168775373297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24968731588219566801990917 4681637172791168775373297)
              ·
                refine ⟨3511227879593376581529973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681637172791168775373297 3511227879593376581529973)
                ·
                  refine ⟨329177613711879054518435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3511227879593376581529973 329177613711879054518435)
                  ·
                    rfl

theorem cell23_5769640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 5].length) (baseStart_5769640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769640 prefixEnd_5769640 := by exact prefixLift 5769640
  have htrace : WordTrace (prefixWord ++ tailWord_5769640) baseStart_5769640 baseEnd_5769640 := by
    simpa [prefixWord, tailWord_5769640, baseEnd_5769640] using wordTrace_append hprefix tailTrace_5769640
  have hstable : (prefixWord ++ tailWord_5769640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769640).length < 2 ^ (prefixWord ++ tailWord_5769640).sum := by decide
  have hdescent : baseEnd_5769640 < baseStart_5769640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769686 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5769686 : Nat := 118140960795 + 5769686 * 2 ^ 59
def prefixEnd_5769686 : Nat := 4983230072969 + 3 ^ 40 * 5769686 * 2
def baseEnd_5769686 : Nat := 2962622143517018310690703

theorem tailTrace_5769686 : CollatzResearch.WordTrace tailWord_5769686 prefixEnd_5769686 2962622143517018310690703 := by
  unfold tailWord_5769686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152358535963780047718057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140291824383613653842325941 13152358535963780047718057)
  ·
    refine ⟨9864268901972835035788543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13152358535963780047718057 9864268901972835035788543)
    ·
      refine ⟨14796403352959252553682815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9864268901972835035788543 14796403352959252553682815)
      ·
        refine ⟨22194605029438878830524223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14796403352959252553682815 22194605029438878830524223)
        ·
          refine ⟨33291907544158318245786335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22194605029438878830524223 33291907544158318245786335)
          ·
            refine ⟨49937861316237477368679503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33291907544158318245786335 49937861316237477368679503)
            ·
              refine ⟨74906791974356216053019255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49937861316237477368679503 74906791974356216053019255)
              ·
                refine ⟨112360187961534324079528883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74906791974356216053019255 112360187961534324079528883)
                ·
                  refine ⟨168540281942301486119293325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112360187961534324079528883 168540281942301486119293325)
                  ·
                    refine ⟨63202605728363057294734997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168540281942301486119293325 63202605728363057294734997)
                    ·
                      refine ⟨2962622143517018310690703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63202605728363057294734997 2962622143517018310690703)
                      ·
                        rfl

theorem cell23_5769686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5769686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769686 prefixEnd_5769686 := by exact prefixLift 5769686
  have htrace : WordTrace (prefixWord ++ tailWord_5769686) baseStart_5769686 baseEnd_5769686 := by
    simpa [prefixWord, tailWord_5769686, baseEnd_5769686] using wordTrace_append hprefix tailTrace_5769686
  have hstable : (prefixWord ++ tailWord_5769686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769686).length < 2 ^ (prefixWord ++ tailWord_5769686).sum := by decide
  have hdescent : baseEnd_5769686 < baseStart_5769686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769790 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_5769790 : Nat := 118140960795 + 5769790 * 2 ^ 59
def prefixEnd_5769790 : Nat := 4983230072969 + 3 ^ 40 * 5769790 * 2
def baseEnd_5769790 : Nat := 987558515168361967930075

theorem tailTrace_5769790 : CollatzResearch.WordTrace tailWord_5769790 prefixEnd_5769790 987558515168361967930075 := by
  unfold tailWord_5769790
  simp only [CollatzResearch.WordTrace]
  refine ⟨26305191220880463315659353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140294353178029137683516549 26305191220880463315659353)
  ·
    refine ⟨19728893415660347486744515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26305191220880463315659353 19728893415660347486744515)
    ·
      refine ⟨29593340123490521230116773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19728893415660347486744515 29593340123490521230116773)
      ·
        refine ⟨5548751273154472730646895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29593340123490521230116773 5548751273154472730646895)
        ·
          refine ⟨8323126909731709095970343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548751273154472730646895 8323126909731709095970343)
          ·
            refine ⟨12484690364597563643955515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8323126909731709095970343 12484690364597563643955515)
            ·
              refine ⟨18727035546896345465933273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12484690364597563643955515 18727035546896345465933273)
              ·
                refine ⟨14045276660172259099449955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18727035546896345465933273 14045276660172259099449955)
                ·
                  refine ⟨21067914990258388649174933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14045276660172259099449955 21067914990258388649174933)
                  ·
                    refine ⟨987558515168361967930075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21067914990258388649174933 987558515168361967930075)
                    ·
                      rfl

theorem cell23_5769790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_5769790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769790 prefixEnd_5769790 := by exact prefixLift 5769790
  have htrace : WordTrace (prefixWord ++ tailWord_5769790) baseStart_5769790 baseEnd_5769790 := by
    simpa [prefixWord, tailWord_5769790, baseEnd_5769790] using wordTrace_append hprefix tailTrace_5769790
  have hstable : (prefixWord ++ tailWord_5769790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769790).length < 2 ^ (prefixWord ++ tailWord_5769790).sum := by decide
  have hdescent : baseEnd_5769790 < baseStart_5769790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769793 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5769793 : Nat := 118140960795 + 5769793 * 2 ^ 59
def prefixEnd_5769793 : Nat := 4983230072969 + 3 ^ 40 * 5769793 * 2
def baseEnd_5769793 : Nat := 2962677085947049392052711

theorem tailTrace_5769793 : CollatzResearch.WordTrace tailWord_5769793 prefixEnd_5769793 2962677085947049392052711 := by
  unfold tailWord_5769793
  simp only [CollatzResearch.WordTrace]
  refine ⟨210441639186032838037634033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140294426124021892025089355 210441639186032838037634033)
  ·
    refine ⟨157831229389524628528225525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210441639186032838037634033 157831229389524628528225525)
    ·
      refine ⟨14796677755267933924521143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157831229389524628528225525 14796677755267933924521143)
      ·
        refine ⟨22195016632901900886781715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14796677755267933924521143 22195016632901900886781715)
        ·
          refine ⟨33292524949352851330172573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22195016632901900886781715 33292524949352851330172573)
          ·
            refine ⟨12484696856007319248814715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33292524949352851330172573 12484696856007319248814715)
            ·
              refine ⟨18727045284010978873222073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12484696856007319248814715 18727045284010978873222073)
              ·
                refine ⟨14045283963008234154916555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18727045284010978873222073 14045283963008234154916555)
                ·
                  refine ⟨21067925944512351232374833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14045283963008234154916555 21067925944512351232374833)
                  ·
                    refine ⟨15800944458384263424281125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21067925944512351232374833 15800944458384263424281125)
                    ·
                      refine ⟨2962677085947049392052711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15800944458384263424281125 2962677085947049392052711)
                      ·
                        rfl

theorem cell23_5769793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5769793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769793 prefixEnd_5769793 := by exact prefixLift 5769793
  have htrace : WordTrace (prefixWord ++ tailWord_5769793) baseStart_5769793 baseEnd_5769793 := by
    simpa [prefixWord, tailWord_5769793, baseEnd_5769793] using wordTrace_append hprefix tailTrace_5769793
  have hstable : (prefixWord ++ tailWord_5769793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769793).length < 2 ^ (prefixWord ++ tailWord_5769793).sum := by decide
  have hdescent : baseEnd_5769793 < baseStart_5769793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769813 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_5769813 : Nat := 118140960795 + 5769813 * 2 ^ 59
def prefixEnd_5769813 : Nat := 4983230072969 + 3 ^ 40 * 5769813 * 2
def baseEnd_5769813 : Nat := 2962687355560139313802619

theorem tailTrace_5769813 : CollatzResearch.WordTrace tailWord_5769813 prefixEnd_5769813 2962687355560139313802619 := by
  unfold tailWord_5769813
  simp only [CollatzResearch.WordTrace]
  refine ⟨210442368645960381453362093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140294912430640254302241395 210442368645960381453362093)
  ·
    refine ⟨78915888242235143045010785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210442368645960381453362093 78915888242235143045010785)
    ·
      refine ⟨59186916181676357283758089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78915888242235143045010785 59186916181676357283758089)
      ·
        refine ⟨44390187136257267962818567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59186916181676357283758089 44390187136257267962818567)
        ·
          refine ⟨66585280704385901944227851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44390187136257267962818567 66585280704385901944227851)
          ·
            refine ⟨99877921056578852916341777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66585280704385901944227851 99877921056578852916341777)
            ·
              refine ⟨74908440792434139687256333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99877921056578852916341777 74908440792434139687256333)
              ·
                refine ⟨28090665297162802382721125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74908440792434139687256333 28090665297162802382721125)
                ·
                  refine ⟨5266999743218025446760211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28090665297162802382721125 5266999743218025446760211)
                  ·
                    refine ⟨7900499614827038170140317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5266999743218025446760211 7900499614827038170140317)
                    ·
                      refine ⟨2962687355560139313802619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7900499614827038170140317 2962687355560139313802619)
                      ·
                        rfl

theorem cell23_5769813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_5769813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769813 prefixEnd_5769813 := by exact prefixLift 5769813
  have htrace : WordTrace (prefixWord ++ tailWord_5769813) baseStart_5769813 baseEnd_5769813 := by
    simpa [prefixWord, tailWord_5769813, baseEnd_5769813] using wordTrace_append hprefix tailTrace_5769813
  have hstable : (prefixWord ++ tailWord_5769813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769813).length < 2 ^ (prefixWord ++ tailWord_5769813).sum := by decide
  have hdescent : baseEnd_5769813 < baseStart_5769813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769820 : List Nat := [2, 2, 4, 1, 4, 1, 1, 8]
def baseStart_5769820 : Nat := 118140960795 + 5769820 * 2 ^ 59
def prefixEnd_5769820 : Nat := 4983230072969 + 3 ^ 40 * 5769820 * 2
def baseEnd_5769820 : Nat := 109729294441656325422781

theorem tailTrace_5769820 : CollatzResearch.WordTrace tailWord_5769820 prefixEnd_5769820 109729294441656325422781 := by
  unfold tailWord_5769820
  simp only [CollatzResearch.WordTrace]
  refine ⟨105221311978467510824433457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140295082637956681099244609 105221311978467510824433457)
  ·
    refine ⟨78915983983850633118325093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105221311978467510824433457 78915983983850633118325093)
    ·
      refine ⟨14796746996971993709685955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78915983983850633118325093 14796746996971993709685955)
      ·
        refine ⟨22195120495457990564528933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14796746996971993709685955 22195120495457990564528933)
        ·
          refine ⟨4161585092898373230849175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22195120495457990564528933 4161585092898373230849175)
          ·
            refine ⟨6242377639347559846273763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161585092898373230849175 6242377639347559846273763)
            ·
              refine ⟨9363566459021339769410645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6242377639347559846273763 9363566459021339769410645)
              ·
                refine ⟨109729294441656325422781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9363566459021339769410645 109729294441656325422781)
                ·
                  rfl

theorem cell23_5769820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 8].length) (baseStart_5769820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769820 prefixEnd_5769820 := by exact prefixLift 5769820
  have htrace : WordTrace (prefixWord ++ tailWord_5769820) baseStart_5769820 baseEnd_5769820 := by
    simpa [prefixWord, tailWord_5769820, baseEnd_5769820] using wordTrace_append hprefix tailTrace_5769820
  have hstable : (prefixWord ++ tailWord_5769820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769820).length < 2 ^ (prefixWord ++ tailWord_5769820).sum := by decide
  have hdescent : baseEnd_5769820 < baseStart_5769820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769858 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5769858 : Nat := 118140960795 + 5769858 * 2 ^ 59
def prefixEnd_5769858 : Nat := 4983230072969 + 3 ^ 40 * 5769858 * 2
def baseEnd_5769858 : Nat := 987570154063197212579971

theorem tailTrace_5769858 : CollatzResearch.WordTrace tailWord_5769858 prefixEnd_5769858 987570154063197212579971 := by
  unfold tailWord_5769858
  simp only [CollatzResearch.WordTrace]
  refine ⟨52611002482699338534687557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140296006620531569425833485 52611002482699338534687557)
  ·
    refine ⟨9864562965506125975253917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52611002482699338534687557 9864562965506125975253917)
    ·
      refine ⟨3699211112064797240720219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9864562965506125975253917 3699211112064797240720219)
      ·
        refine ⟨5548816668097195861080329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699211112064797240720219 5548816668097195861080329)
        ·
          refine ⟨4161612501072896895810247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5548816668097195861080329 4161612501072896895810247)
          ·
            refine ⟨6242418751609345343715371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161612501072896895810247 6242418751609345343715371)
            ·
              refine ⟨9363628127414018015573057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6242418751609345343715371 9363628127414018015573057)
              ·
                refine ⟨7022721095560513511679793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9363628127414018015573057 7022721095560513511679793)
                ·
                  refine ⟨5267040821670385133759845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7022721095560513511679793 5267040821670385133759845)
                  ·
                    refine ⟨987570154063197212579971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5267040821670385133759845 987570154063197212579971)
                    ·
                      rfl

theorem cell23_5769858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5769858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769858 prefixEnd_5769858 := by exact prefixLift 5769858
  have htrace : WordTrace (prefixWord ++ tailWord_5769858) baseStart_5769858 baseEnd_5769858 := by
    simpa [prefixWord, tailWord_5769858, baseEnd_5769858] using wordTrace_append hprefix tailTrace_5769858
  have hstable : (prefixWord ++ tailWord_5769858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769858).length < 2 ^ (prefixWord ++ tailWord_5769858).sum := by decide
  have hdescent : baseEnd_5769858 < baseStart_5769858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769913 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 1, 7, 2]
def baseStart_5769913 : Nat := 118140960795 + 5769913 * 2 ^ 59
def prefixEnd_5769913 : Nat := 4983230072969 + 3 ^ 40 * 5769913 * 2
def baseEnd_5769913 : Nat := 2962738703625588922552159

theorem tailTrace_5769913 : CollatzResearch.WordTrace tailWord_5769913 prefixEnd_5769913 2962738703625588922552159 := by
  unfold tailWord_5769913
  simp only [CollatzResearch.WordTrace]
  refine ⟨210446015945598098532002393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140297343963732065688001595 210446015945598098532002393)
  ·
    refine ⟨157834511959198573899001795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210446015945598098532002393 157834511959198573899001795)
    ·
      refine ⟨236751767938797860848502693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157834511959198573899001795 236751767938797860848502693)
      ·
        refine ⟨44390956488524598909094255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236751767938797860848502693 44390956488524598909094255)
        ·
          refine ⟨66586434732786898363641383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44390956488524598909094255 66586434732786898363641383)
          ·
            refine ⟨99879652099180347545462075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66586434732786898363641383 99879652099180347545462075)
            ·
              refine ⟨149819478148770521318193113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99879652099180347545462075 149819478148770521318193113)
              ·
                refine ⟨112364608611577890988644835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149819478148770521318193113 112364608611577890988644835)
                ·
                  refine ⟨168546912917366836482967253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112364608611577890988644835 168546912917366836482967253)
                  ·
                    refine ⟨3950318271500785230069545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168546912917366836482967253 3950318271500785230069545)
                    ·
                      refine ⟨2962738703625588922552159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3950318271500785230069545 2962738703625588922552159)
                      ·
                        rfl

theorem cell23_5769913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_5769913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769913 prefixEnd_5769913 := by exact prefixLift 5769913
  have htrace : WordTrace (prefixWord ++ tailWord_5769913) baseStart_5769913 baseEnd_5769913 := by
    simpa [prefixWord, tailWord_5769913, baseEnd_5769913] using wordTrace_append hprefix tailTrace_5769913
  have hstable : (prefixWord ++ tailWord_5769913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769913).length < 2 ^ (prefixWord ++ tailWord_5769913).sum := by decide
  have hdescent : baseEnd_5769913 < baseStart_5769913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769938 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_5769938 : Nat := 118140960795 + 5769938 * 2 ^ 59
def prefixEnd_5769938 : Nat := 4983230072969 + 3 ^ 40 * 5769938 * 2
def baseEnd_5769938 : Nat := 2962751540641951324739545

theorem tailTrace_5769938 : CollatzResearch.WordTrace tailWord_5769938 prefixEnd_5769938 2962751540641951324739545 := by
  unfold tailWord_5769938
  simp only [CollatzResearch.WordTrace]
  refine ⟨52611731942626881950415617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140297951847005018534441645 52611731942626881950415617)
  ·
    refine ⟨39458798956970161462811713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52611731942626881950415617 39458798956970161462811713)
    ·
      refine ⟨29594099217727621097108785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39458798956970161462811713 29594099217727621097108785)
      ·
        refine ⟨22195574413295715822831589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29594099217727621097108785 22195574413295715822831589)
        ·
          refine ⟨4161670202492946716780923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22195574413295715822831589 4161670202492946716780923)
          ·
            refine ⟨6242505303739420075171385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161670202492946716780923 6242505303739420075171385)
            ·
              refine ⟨4681878977804565056378539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6242505303739420075171385 4681878977804565056378539)
              ·
                refine ⟨7022818466706847584567809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4681878977804565056378539 7022818466706847584567809)
                ·
                  refine ⟨5267113850030135688425857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7022818466706847584567809 5267113850030135688425857)
                  ·
                    refine ⟨3950335387522601766319393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5267113850030135688425857 3950335387522601766319393)
                    ·
                      refine ⟨2962751540641951324739545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3950335387522601766319393 2962751540641951324739545)
                      ·
                        rfl

theorem cell23_5769938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_5769938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769938 prefixEnd_5769938 := by exact prefixLift 5769938
  have htrace : WordTrace (prefixWord ++ tailWord_5769938) baseStart_5769938 baseEnd_5769938 := by
    simpa [prefixWord, tailWord_5769938, baseEnd_5769938] using wordTrace_append hprefix tailTrace_5769938
  have hstable : (prefixWord ++ tailWord_5769938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769938).length < 2 ^ (prefixWord ++ tailWord_5769938).sum := by decide
  have hdescent : baseEnd_5769938 < baseStart_5769938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5769980 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_5769980 : Nat := 118140960795 + 5769980 * 2 ^ 59
def prefixEnd_5769980 : Nat := 4983230072969 + 3 ^ 40 * 5769980 * 2
def baseEnd_5769980 : Nat := 2962773106829440160414351

theorem tailTrace_5769980 : CollatzResearch.WordTrace tailWord_5769980 prefixEnd_5769980 2962773106829440160414351 := by
  unfold tailWord_5769980
  simp only [CollatzResearch.WordTrace]
  refine ⟨105224229818177684487345697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140298973090903579316460929 105224229818177684487345697)
  ·
    refine ⟨78918172363633263365509273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105224229818177684487345697 78918172363633263365509273)
    ·
      refine ⟨59188629272724947524131955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78918172363633263365509273 59188629272724947524131955)
      ·
        refine ⟨88782943909087421286197933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59188629272724947524131955 88782943909087421286197933)
        ·
          refine ⟨33293603965907782982324225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88782943909087421286197933 33293603965907782982324225)
          ·
            refine ⟨24970202974430837236743169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33293603965907782982324225 24970202974430837236743169)
            ·
              refine ⟨18727652230823127927557377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24970202974430837236743169 18727652230823127927557377)
              ·
                refine ⟨14045739173117345945668033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18727652230823127927557377 14045739173117345945668033)
                ·
                  refine ⟨10534304379838009459251025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14045739173117345945668033 10534304379838009459251025)
                  ·
                    refine ⟨7900728284878507094438269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10534304379838009459251025 7900728284878507094438269)
                    ·
                      refine ⟨2962773106829440160414351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7900728284878507094438269 2962773106829440160414351)
                      ·
                        rfl

theorem cell23_5769980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_5769980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5769980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5769980 prefixEnd_5769980 := by exact prefixLift 5769980
  have htrace : WordTrace (prefixWord ++ tailWord_5769980) baseStart_5769980 baseEnd_5769980 := by
    simpa [prefixWord, tailWord_5769980, baseEnd_5769980] using wordTrace_append hprefix tailTrace_5769980
  have hstable : (prefixWord ++ tailWord_5769980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5769980).length < 2 ^ (prefixWord ++ tailWord_5769980).sum := by decide
  have hdescent : baseEnd_5769980 < baseStart_5769980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5769980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770027 : List Nat := [1, 1, 1, 1, 2, 1, 2, 9, 1, 1, 3]
def baseStart_5770027 : Nat := 118140960795 + 5770027 * 2 ^ 59
def prefixEnd_5770027 : Nat := 4983230072969 + 3 ^ 40 * 5770027 * 2
def baseEnd_5770027 : Nat := 2962797240420201476526635

theorem tailTrace_5770027 : CollatzResearch.WordTrace tailWord_5770027 prefixEnd_5770027 2962797240420201476526635 := by
  unfold tailWord_5770027
  simp only [CollatzResearch.WordTrace]
  refine ⟨210450173867185096001652335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140300115911456730667768223 210450173867185096001652335)
  ·
    refine ⟨315675260800777644002478503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210450173867185096001652335 315675260800777644002478503)
    ·
      refine ⟨473512891201166466003717755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315675260800777644002478503 473512891201166466003717755)
      ·
        refine ⟨710269336801749699005576633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473512891201166466003717755 710269336801749699005576633)
        ·
          refine ⟨532702002601312274254182475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710269336801749699005576633 532702002601312274254182475)
          ·
            refine ⟨799053003901968411381273713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532702002601312274254182475 799053003901968411381273713)
            ·
              refine ⟨599289752926476308535955285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799053003901968411381273713 599289752926476308535955285)
              ·
                refine ⟨3511463396053572120327863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 599289752926476308535955285 3511463396053572120327863)
                ·
                  refine ⟨5267195094080358180491795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511463396053572120327863 5267195094080358180491795)
                  ·
                    refine ⟨7900792641120537270737693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5267195094080358180491795 7900792641120537270737693)
                    ·
                      refine ⟨2962797240420201476526635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7900792641120537270737693 2962797240420201476526635)
                      ·
                        rfl

theorem cell23_5770027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 1, 3].length) (baseStart_5770027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770027 prefixEnd_5770027 := by exact prefixLift 5770027
  have htrace : WordTrace (prefixWord ++ tailWord_5770027) baseStart_5770027 baseEnd_5770027 := by
    simpa [prefixWord, tailWord_5770027, baseEnd_5770027] using wordTrace_append hprefix tailTrace_5770027
  have hstable : (prefixWord ++ tailWord_5770027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770027).length < 2 ^ (prefixWord ++ tailWord_5770027).sum := by decide
  have hdescent : baseEnd_5770027 < baseStart_5770027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770053 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_5770053 : Nat := 118140960795 + 5770053 * 2 ^ 59
def prefixEnd_5770053 : Nat := 4983230072969 + 3 ^ 40 * 5770053 * 2
def baseEnd_5770053 : Nat := 2962810590917218374801515

theorem tailTrace_5770053 : CollatzResearch.WordTrace tailWord_5770053 prefixEnd_5770053 2962810590917218374801515 := by
  unfold tailWord_5770053
  simp only [CollatzResearch.WordTrace]
  refine ⟨210451122165090902442098813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140300748110060601628065875 210451122165090902442098813)
  ·
    refine ⟨78919170811909088415787055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210451122165090902442098813 78919170811909088415787055)
    ·
      refine ⟨118378756217863632623680583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78919170811909088415787055 118378756217863632623680583)
      ·
        refine ⟨177568134326795448935520875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118378756217863632623680583 177568134326795448935520875)
        ·
          refine ⟨266352201490193173403281313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177568134326795448935520875 266352201490193173403281313)
          ·
            refine ⟨199764151117644880052460985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266352201490193173403281313 199764151117644880052460985)
            ·
              refine ⟨149823113338233660039345739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199764151117644880052460985 149823113338233660039345739)
              ·
                refine ⟨224734670007350490059018609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149823113338233660039345739 224734670007350490059018609)
                ·
                  refine ⟨168551002505512867544263957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224734670007350490059018609 168551002505512867544263957)
                  ·
                    refine ⟨7900828242445915666137373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 168551002505512867544263957 7900828242445915666137373)
                    ·
                      refine ⟨2962810590917218374801515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7900828242445915666137373 2962810590917218374801515)
                      ·
                        rfl

theorem cell23_5770053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_5770053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770053 prefixEnd_5770053 := by exact prefixLift 5770053
  have htrace : WordTrace (prefixWord ++ tailWord_5770053) baseStart_5770053 baseEnd_5770053 := by
    simpa [prefixWord, tailWord_5770053, baseEnd_5770053] using wordTrace_append hprefix tailTrace_5770053
  have hstable : (prefixWord ++ tailWord_5770053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770053).length < 2 ^ (prefixWord ++ tailWord_5770053).sum := by decide
  have hdescent : baseEnd_5770053 < baseStart_5770053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770060 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_5770060 : Nat := 118140960795 + 5770060 * 2 ^ 59
def prefixEnd_5770060 : Nat := 4983230072969 + 3 ^ 40 * 5770060 * 2
def baseEnd_5770060 : Nat := 987604728427266615804661

theorem tailTrace_5770060 : CollatzResearch.WordTrace tailWord_5770060 prefixEnd_5770060 987604728427266615804661 := by
  unfold tailWord_5770060
  simp only [CollatzResearch.WordTrace]
  refine ⟨105225688738032771318801817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140300918317377028425069089 105225688738032771318801817)
  ·
    refine ⟨78919266553524578489101363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105225688738032771318801817 78919266553524578489101363)
    ·
      refine ⟨118378899830286867733652045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78919266553524578489101363 118378899830286867733652045)
      ·
        refine ⟨44392087436357575400119517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118378899830286867733652045 44392087436357575400119517)
        ·
          refine ⟨16647032788634090775044819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44392087436357575400119517 16647032788634090775044819)
          ·
            refine ⟨24970549182951136162567229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16647032788634090775044819 24970549182951136162567229)
            ·
              refine ⟨9363955943606676060962711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24970549182951136162567229 9363955943606676060962711)
              ·
                refine ⟨14045933915410014091444067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9363955943606676060962711 14045933915410014091444067)
                ·
                  refine ⟨21068900873115021137166101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14045933915410014091444067 21068900873115021137166101)
                  ·
                    refine ⟨987604728427266615804661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21068900873115021137166101 987604728427266615804661)
                    ·
                      rfl

theorem cell23_5770060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_5770060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770060 prefixEnd_5770060 := by exact prefixLift 5770060
  have htrace : WordTrace (prefixWord ++ tailWord_5770060) baseStart_5770060 baseEnd_5770060 := by
    simpa [prefixWord, tailWord_5770060, baseEnd_5770060] using wordTrace_append hprefix tailTrace_5770060
  have hstable : (prefixWord ++ tailWord_5770060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770060).length < 2 ^ (prefixWord ++ tailWord_5770060).sum := by decide
  have hdescent : baseEnd_5770060 < baseStart_5770060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770073 : List Nat := [1, 2, 1, 2, 2, 5, 1, 9]
def baseStart_5770073 : Nat := 118140960795 + 5770073 * 2 ^ 59
def prefixEnd_5770073 : Nat := 4983230072969 + 3 ^ 40 * 5770073 * 2
def baseEnd_5770073 : Nat := 109734105945566973946349

theorem tailTrace_5770073 : CollatzResearch.WordTrace tailWord_5770073 prefixEnd_5770073 109734105945566973946349 := by
  unfold tailWord_5770073
  simp only [CollatzResearch.WordTrace]
  refine ⟨210451851625018445857826873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140301234416678963905217915 210451851625018445857826873)
  ·
    refine ⟨157838888718763834393370155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210451851625018445857826873 157838888718763834393370155)
    ·
      refine ⟨236758333078145751590055233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157838888718763834393370155 236758333078145751590055233)
      ·
        refine ⟨177568749808609313692541425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236758333078145751590055233 177568749808609313692541425)
        ·
          refine ⟨133176562356456985269406069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177568749808609313692541425 133176562356456985269406069)
          ·
            refine ⟨12485302720917842369006819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133176562356456985269406069 12485302720917842369006819)
            ·
              refine ⟨18727954081376763553510229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12485302720917842369006819 18727954081376763553510229)
              ·
                refine ⟨109734105945566973946349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18727954081376763553510229 109734105945566973946349)
                ·
                  rfl

theorem cell23_5770073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 9].length) (baseStart_5770073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770073 prefixEnd_5770073 := by exact prefixLift 5770073
  have htrace : WordTrace (prefixWord ++ tailWord_5770073) baseStart_5770073 baseEnd_5770073 := by
    simpa [prefixWord, tailWord_5770073, baseEnd_5770073] using wordTrace_append hprefix tailTrace_5770073
  have hstable : (prefixWord ++ tailWord_5770073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770073).length < 2 ^ (prefixWord ++ tailWord_5770073).sum := by decide
  have hdescent : baseEnd_5770073 < baseStart_5770073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770087 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_5770087 : Nat := 118140960795 + 5770087 * 2 ^ 59
def prefixEnd_5770087 : Nat := 4983230072969 + 3 ^ 40 * 5770087 * 2
def baseEnd_5770087 : Nat := 2962828049259471241776359

theorem tailTrace_5770087 : CollatzResearch.WordTrace tailWord_5770087 prefixEnd_5770087 2962828049259471241776359 := by
  unfold tailWord_5770087
  simp only [CollatzResearch.WordTrace]
  refine ⟨210452362246967726248836515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140301574831311817499224343 210452362246967726248836515)
  ·
    refine ⟨315678543370451589373254773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210452362246967726248836515 315678543370451589373254773)
    ·
      refine ⟨29594863440979836503742635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 315678543370451589373254773 29594863440979836503742635)
      ·
        refine ⟨44392295161469754755613953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29594863440979836503742635 44392295161469754755613953)
        ·
          refine ⟨33294221371102316066710465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44392295161469754755613953 33294221371102316066710465)
          ·
            refine ⟨24970666028326737050032849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33294221371102316066710465 24970666028326737050032849)
            ·
              refine ⟨18727999521245052787524637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24970666028326737050032849 18727999521245052787524637)
              ·
                refine ⟨7022999820466894795321739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18727999521245052787524637 7022999820466894795321739)
                ·
                  refine ⟨10534499730700342192982609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7022999820466894795321739 10534499730700342192982609)
                  ·
                    refine ⟨7900874798025256644736957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10534499730700342192982609 7900874798025256644736957)
                    ·
                      refine ⟨2962828049259471241776359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7900874798025256644736957 2962828049259471241776359)
                      ·
                        rfl

theorem cell23_5770087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_5770087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770087 prefixEnd_5770087 := by exact prefixLift 5770087
  have htrace : WordTrace (prefixWord ++ tailWord_5770087) baseStart_5770087 baseEnd_5770087 := by
    simpa [prefixWord, tailWord_5770087, baseEnd_5770087] using wordTrace_append hprefix tailTrace_5770087
  have hstable : (prefixWord ++ tailWord_5770087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770087).length < 2 ^ (prefixWord ++ tailWord_5770087).sum := by decide
  have hdescent : baseEnd_5770087 < baseStart_5770087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770101 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_5770101 : Nat := 118140960795 + 5770101 * 2 ^ 59
def prefixEnd_5770101 : Nat := 4983230072969 + 3 ^ 40 * 5770101 * 2
def baseEnd_5770101 : Nat := 2962835237988634187001295

theorem tailTrace_5770101 : CollatzResearch.WordTrace tailWord_5770101 prefixEnd_5770101 2962835237988634187001295 := by
  unfold tailWord_5770101
  simp only [CollatzResearch.WordTrace]
  refine ⟨210452872868917006639846157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140301915245944671093230771 210452872868917006639846157)
  ·
    refine ⟨78919827325843877489942309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210452872868917006639846157 78919827325843877489942309)
    ·
      refine ⟨14797467623595727029364183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78919827325843877489942309 14797467623595727029364183)
      ·
        refine ⟨22196201435393590544046275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14797467623595727029364183 22196201435393590544046275)
        ·
          refine ⟨33294302153090385816069413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22196201435393590544046275 33294302153090385816069413)
          ·
            refine ⟨6242681653704447340513015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33294302153090385816069413 6242681653704447340513015)
            ·
              refine ⟨9364022480556671010769523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6242681653704447340513015 9364022480556671010769523)
              ·
                refine ⟨14046033720835006516154285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9364022480556671010769523 14046033720835006516154285)
                ·
                  refine ⟨5267262645313127443557857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14046033720835006516154285 5267262645313127443557857)
                  ·
                    refine ⟨3950446983984845582668393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5267262645313127443557857 3950446983984845582668393)
                    ·
                      refine ⟨2962835237988634187001295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3950446983984845582668393 2962835237988634187001295)
                      ·
                        rfl

theorem cell23_5770101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_5770101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770101 prefixEnd_5770101 := by exact prefixLift 5770101
  have htrace : WordTrace (prefixWord ++ tailWord_5770101) baseStart_5770101 baseEnd_5770101 := by
    simpa [prefixWord, tailWord_5770101, baseEnd_5770101] using wordTrace_append hprefix tailTrace_5770101
  have hstable : (prefixWord ++ tailWord_5770101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770101).length < 2 ^ (prefixWord ++ tailWord_5770101).sum := by decide
  have hdescent : baseEnd_5770101 < baseStart_5770101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770151 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_5770151 : Nat := 118140960795 + 5770151 * 2 ^ 59
def prefixEnd_5770151 : Nat := 4983230072969 + 3 ^ 40 * 5770151 * 2
def baseEnd_5770151 : Nat := 2962860912021358991376065

theorem tailTrace_5770151 : CollatzResearch.WordTrace tailWord_5770151 prefixEnd_5770151 2962860912021358991376065 := by
  unfold tailWord_5770151
  simp only [CollatzResearch.WordTrace]
  refine ⟨210454696518735865179166307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140303131012490576786110871 210454696518735865179166307)
  ·
    refine ⟨315682044778103797768749461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210454696518735865179166307 315682044778103797768749461)
    ·
      refine ⟨14797595848973615520410131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 315682044778103797768749461 14797595848973615520410131)
      ·
        refine ⟨22196393773460423280615197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14797595848973615520410131 22196393773460423280615197)
        ·
          refine ⟨8323647665047658730230699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22196393773460423280615197 8323647665047658730230699)
          ·
            refine ⟨12485471497571488095346049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8323647665047658730230699 12485471497571488095346049)
            ·
              refine ⟨9364103623178616071509537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12485471497571488095346049 9364103623178616071509537)
              ·
                refine ⟨7023077717383962053632153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9364103623178616071509537 7023077717383962053632153)
                ·
                  refine ⟨5267308288037971540224115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7023077717383962053632153 5267308288037971540224115)
                  ·
                    refine ⟨7900962432056957310336173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5267308288037971540224115 7900962432056957310336173)
                    ·
                      refine ⟨2962860912021358991376065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7900962432056957310336173 2962860912021358991376065)
                      ·
                        rfl

theorem cell23_5770151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_5770151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770151 prefixEnd_5770151 := by exact prefixLift 5770151
  have htrace : WordTrace (prefixWord ++ tailWord_5770151) baseStart_5770151 baseEnd_5770151 := by
    simpa [prefixWord, tailWord_5770151, baseEnd_5770151] using wordTrace_append hprefix tailTrace_5770151
  have hstable : (prefixWord ++ tailWord_5770151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770151).length < 2 ^ (prefixWord ++ tailWord_5770151).sum := by decide
  have hdescent : baseEnd_5770151 < baseStart_5770151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770170 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_5770170 : Nat := 118140960795 + 5770170 * 2 ^ 59
def prefixEnd_5770170 : Nat := 4983230072969 + 3 ^ 40 * 5770170 * 2
def baseEnd_5770170 : Nat := 2962870668153794417038477

theorem tailTrace_5770170 : CollatzResearch.WordTrace tailWord_5770170 prefixEnd_5770170 2962870668153794417038477 := by
  unfold tailWord_5770170
  simp only [CollatzResearch.WordTrace]
  refine ⟨52613847376416757856026991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140303593003778020949405309 52613847376416757856026991)
  ·
    refine ⟨78920771064625136784040487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52613847376416757856026991 78920771064625136784040487)
    ·
      refine ⟨118381156596937705176060731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78920771064625136784040487 118381156596937705176060731)
      ·
        refine ⟨177571734895406557764091097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118381156596937705176060731 177571734895406557764091097)
        ·
          refine ⟨133178801171554918323068323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177571734895406557764091097 133178801171554918323068323)
          ·
            refine ⟨199768201757332377484602485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133178801171554918323068323 199768201757332377484602485)
            ·
              refine ⟨18728268914749910389181483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199768201757332377484602485 18728268914749910389181483)
              ·
                refine ⟨28092403372124865583772225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18728268914749910389181483 28092403372124865583772225)
                ·
                  refine ⟨21069302529093649187829169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28092403372124865583772225 21069302529093649187829169)
                  ·
                    refine ⟨15801976896820236890871877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21069302529093649187829169 15801976896820236890871877)
                    ·
                      refine ⟨2962870668153794417038477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15801976896820236890871877 2962870668153794417038477)
                      ·
                        rfl

theorem cell23_5770170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_5770170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770170 prefixEnd_5770170 := by exact prefixLift 5770170
  have htrace : WordTrace (prefixWord ++ tailWord_5770170) baseStart_5770170 baseEnd_5770170 := by
    simpa [prefixWord, tailWord_5770170, baseEnd_5770170] using wordTrace_append hprefix tailTrace_5770170
  have hstable : (prefixWord ++ tailWord_5770170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770170).length < 2 ^ (prefixWord ++ tailWord_5770170).sum := by decide
  have hdescent : baseEnd_5770170 < baseStart_5770170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770174 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_5770174 : Nat := 118140960795 + 5770174 * 2 ^ 59
def prefixEnd_5770174 : Nat := 4983230072969 + 3 ^ 40 * 5770174 * 2
def baseEnd_5770174 : Nat := 2962872722076412401388459

theorem tailTrace_5770174 : CollatzResearch.WordTrace tailWord_5770174 prefixEnd_5770174 2962872722076412401388459 := by
  unfold tailWord_5770174
  simp only [CollatzResearch.WordTrace]
  refine ⟨26306941924706567513406697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140303690265101693404835717 26306941924706567513406697)
  ·
    refine ⟨19730206443529925635055023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26306941924706567513406697 19730206443529925635055023)
    ·
      refine ⟨29595309665294888452582535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19730206443529925635055023 29595309665294888452582535)
      ·
        refine ⟨44392964497942332678873803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29595309665294888452582535 44392964497942332678873803)
        ·
          refine ⟨66589446746913499018310705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44392964497942332678873803 66589446746913499018310705)
          ·
            refine ⟨49942085060185124263733029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66589446746913499018310705 49942085060185124263733029)
            ·
              refine ⟨9364140948784710799449943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49942085060185124263733029 9364140948784710799449943)
              ·
                refine ⟨14046211423177066199174915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9364140948784710799449943 14046211423177066199174915)
                ·
                  refine ⟨21069317134765599298762373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14046211423177066199174915 21069317134765599298762373)
                  ·
                    refine ⟨3950496962768549868517945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21069317134765599298762373 3950496962768549868517945)
                    ·
                      refine ⟨2962872722076412401388459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3950496962768549868517945 2962872722076412401388459)
                      ·
                        rfl

theorem cell23_5770174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_5770174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770174 prefixEnd_5770174 := by exact prefixLift 5770174
  have htrace : WordTrace (prefixWord ++ tailWord_5770174) baseStart_5770174 baseEnd_5770174 := by
    simpa [prefixWord, tailWord_5770174, baseEnd_5770174] using wordTrace_append hprefix tailTrace_5770174
  have hstable : (prefixWord ++ tailWord_5770174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770174).length < 2 ^ (prefixWord ++ tailWord_5770174).sum := by decide
  have hdescent : baseEnd_5770174 < baseStart_5770174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770247 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5770247 : Nat := 118140960795 + 5770247 * 2 ^ 59
def prefixEnd_5770247 : Nat := 4983230072969 + 3 ^ 40 * 5770247 * 2
def baseEnd_5770247 : Nat := 2962910206164190615775623

theorem tailTrace_5770247 : CollatzResearch.WordTrace tailWord_5770247 prefixEnd_5770247 2962910206164190615775623 := by
  unfold tailWord_5770247
  simp only [CollatzResearch.WordTrace]
  refine ⟨210458197926388073574660995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140305465284258715716440663 210458197926388073574660995)
  ·
    refine ⟨315687296889582110361991493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210458197926388073574660995 315687296889582110361991493)
    ·
      refine ⟨59191368166796645692873405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315687296889582110361991493 59191368166796645692873405)
      ·
        refine ⟨22196763062548742134827527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59191368166796645692873405 22196763062548742134827527)
        ·
          refine ⟨33295144593823113202241291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22196763062548742134827527 33295144593823113202241291)
          ·
            refine ⟨49942716890734669803361937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33295144593823113202241291 49942716890734669803361937)
            ·
              refine ⟨37457037668051002352521453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49942716890734669803361937 37457037668051002352521453)
              ·
                refine ⟨14046389125519125882195545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37457037668051002352521453 14046389125519125882195545)
                ·
                  refine ⟨10534791844139344411646659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14046389125519125882195545 10534791844139344411646659)
                  ·
                    refine ⟨15802187766209016617469989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10534791844139344411646659 15802187766209016617469989)
                    ·
                      refine ⟨2962910206164190615775623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15802187766209016617469989 2962910206164190615775623)
                      ·
                        rfl

theorem cell23_5770247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5770247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770247 prefixEnd_5770247 := by exact prefixLift 5770247
  have htrace : WordTrace (prefixWord ++ tailWord_5770247) baseStart_5770247 baseEnd_5770247 := by
    simpa [prefixWord, tailWord_5770247, baseEnd_5770247] using wordTrace_append hprefix tailTrace_5770247
  have hstable : (prefixWord ++ tailWord_5770247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770247).length < 2 ^ (prefixWord ++ tailWord_5770247).sum := by decide
  have hdescent : baseEnd_5770247 < baseStart_5770247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770274 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_5770274 : Nat := 118140960795 + 5770274 * 2 ^ 59
def prefixEnd_5770274 : Nat := 4983230072969 + 3 ^ 40 * 5770274 * 2
def baseEnd_5770274 : Nat := 987641356713954003379333

theorem tailTrace_5770274 : CollatzResearch.WordTrace tailWord_5770274 prefixEnd_5770274 987641356713954003379333 := by
  unfold tailWord_5770274
  simp only [CollatzResearch.WordTrace]
  refine ⟨52614795674322564296473469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140306121798193504790595917 52614795674322564296473469)
  ·
    refine ⟨19730548377870961611177551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52614795674322564296473469 19730548377870961611177551)
    ·
      refine ⟨29595822566806442416766327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19730548377870961611177551 29595822566806442416766327)
      ·
        refine ⟨44393733850209663625149491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29595822566806442416766327 44393733850209663625149491)
        ·
          refine ⟨66590600775314495437724237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44393733850209663625149491 66590600775314495437724237)
          ·
            refine ⟨24971475290742935789146589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66590600775314495437724237 24971475290742935789146589)
            ·
              refine ⟨9364303234028600920929971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24971475290742935789146589 9364303234028600920929971)
              ·
                refine ⟨14046454851042901381394957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9364303234028600920929971 14046454851042901381394957)
                ·
                  refine ⟨5267420569141088018023109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14046454851042901381394957 5267420569141088018023109)
                  ·
                    refine ⟨987641356713954003379333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5267420569141088018023109 987641356713954003379333)
                    ·
                      rfl

theorem cell23_5770274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_5770274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770274 prefixEnd_5770274 := by exact prefixLift 5770274
  have htrace : WordTrace (prefixWord ++ tailWord_5770274) baseStart_5770274 baseEnd_5770274 := by
    simpa [prefixWord, tailWord_5770274, baseEnd_5770274] using wordTrace_append hprefix tailTrace_5770274
  have hstable : (prefixWord ++ tailWord_5770274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770274).length < 2 ^ (prefixWord ++ tailWord_5770274).sum := by decide
  have hdescent : baseEnd_5770274 < baseStart_5770274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770337 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_5770337 : Nat := 118140960795 + 5770337 * 2 ^ 59
def prefixEnd_5770337 : Nat := 4983230072969 + 3 ^ 40 * 5770337 * 2
def baseEnd_5770337 : Nat := 2962956419423095263650209

theorem tailTrace_5770337 : CollatzResearch.WordTrace tailWord_5770337 prefixEnd_5770337 2962956419423095263650209 := by
  unfold tailWord_5770337
  simp only [CollatzResearch.WordTrace]
  refine ⟨210461480496062018945437265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140307653664041345963624843 210461480496062018945437265)
  ·
    refine ⟨157846110372046514209077949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210461480496062018945437265 157846110372046514209077949)
    ·
      refine ⟨59192291389517442828404231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157846110372046514209077949 59192291389517442828404231)
      ·
        refine ⟨88788437084276164242606347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59192291389517442828404231 88788437084276164242606347)
        ·
          refine ⟨133182655626414246363909521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88788437084276164242606347 133182655626414246363909521)
          ·
            refine ⟨99886991719810684772932141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133182655626414246363909521 99886991719810684772932141)
            ·
              refine ⟨37457621894929006789849553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99886991719810684772932141 37457621894929006789849553)
              ·
                refine ⟨28093216421196755092387165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37457621894929006789849553 28093216421196755092387165)
                ·
                  refine ⟨10534956157948783159645187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28093216421196755092387165 10534956157948783159645187)
                  ·
                    refine ⟨15802434236923174739467781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10534956157948783159645187 15802434236923174739467781)
                    ·
                      refine ⟨2962956419423095263650209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15802434236923174739467781 2962956419423095263650209)
                      ·
                        rfl

theorem cell23_5770337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_5770337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770337 prefixEnd_5770337 := by exact prefixLift 5770337
  have htrace : WordTrace (prefixWord ++ tailWord_5770337) baseStart_5770337 baseEnd_5770337 := by
    simpa [prefixWord, tailWord_5770337, baseEnd_5770337] using wordTrace_append hprefix tailTrace_5770337
  have hstable : (prefixWord ++ tailWord_5770337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770337).length < 2 ^ (prefixWord ++ tailWord_5770337).sum := by decide
  have hdescent : baseEnd_5770337 < baseStart_5770337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770354 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_5770354 : Nat := 118140960795 + 5770354 * 2 ^ 59
def prefixEnd_5770354 : Nat := 4983230072969 + 3 ^ 40 * 5770354 * 2
def baseEnd_5770354 : Nat := 2962965148594221697137631

theorem tailTrace_5770354 : CollatzResearch.WordTrace tailWord_5770354 prefixEnd_5770354 2962965148594221697137631 := by
  unfold tailWord_5770354
  simp only [CollatzResearch.WordTrace]
  refine ⟨52615525134250107712201529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140308067024666953899204077 52615525134250107712201529)
  ·
    refine ⟨39461643850687580784151147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52615525134250107712201529 39461643850687580784151147)
    ·
      refine ⟨59192465776031371176226721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39461643850687580784151147 59192465776031371176226721)
      ·
        refine ⟨44394349332023528382170041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59192465776031371176226721 44394349332023528382170041)
        ·
          refine ⟨33295761999017646286627531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44394349332023528382170041 33295761999017646286627531)
          ·
            refine ⟨49943642998526469429941297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33295761999017646286627531 49943642998526469429941297)
            ·
              refine ⟨37457732248894852072455973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49943642998526469429941297 37457732248894852072455973)
              ·
                refine ⟨7023324796667784763585495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37457732248894852072455973 7023324796667784763585495)
                ·
                  refine ⟨10534987195001677145378243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7023324796667784763585495 10534987195001677145378243)
                  ·
                    refine ⟨15802480792502515718067365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10534987195001677145378243 15802480792502515718067365)
                    ·
                      refine ⟨2962965148594221697137631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15802480792502515718067365 2962965148594221697137631)
                      ·
                        rfl

theorem cell23_5770354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_5770354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770354 prefixEnd_5770354 := by exact prefixLift 5770354
  have htrace : WordTrace (prefixWord ++ tailWord_5770354) baseStart_5770354 baseEnd_5770354 := by
    simpa [prefixWord, tailWord_5770354, baseEnd_5770354] using wordTrace_append hprefix tailTrace_5770354
  have hstable : (prefixWord ++ tailWord_5770354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770354).length < 2 ^ (prefixWord ++ tailWord_5770354).sum := by decide
  have hdescent : baseEnd_5770354 < baseStart_5770354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770360 : List Nat := [2, 1, 2, 1, 1, 1, 4, 11]
def baseStart_5770360 : Nat := 118140960795 + 5770360 * 2 ^ 59
def prefixEnd_5770360 : Nat := 4983230072969 + 3 ^ 40 * 5770360 * 2
def baseEnd_5770360 : Nat := 109739564054746247172689

theorem tailTrace_5770360 : CollatzResearch.WordTrace tailWord_5770360 prefixEnd_5770360 109739564054746247172689 := by
  unfold tailWord_5770360
  simp only [CollatzResearch.WordTrace]
  refine ⟨105231159687489346936762267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140308212916652462582349689 105231159687489346936762267)
  ·
    refine ⟨157846739531234020405143401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105231159687489346936762267 157846739531234020405143401)
    ·
      refine ⟨118385054648425515303857551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157846739531234020405143401 118385054648425515303857551)
      ·
        refine ⟨177577581972638272955786327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118385054648425515303857551 177577581972638272955786327)
        ·
          refine ⟨266366372958957409433679491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177577581972638272955786327 266366372958957409433679491)
          ·
            refine ⟨399549559438436114150519237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266366372958957409433679491 399549559438436114150519237)
            ·
              refine ⟨74915542394706771403222357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399549559438436114150519237 74915542394706771403222357)
              ·
                refine ⟨109739564054746247172689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74915542394706771403222357 109739564054746247172689)
                ·
                  rfl

theorem cell23_5770360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 11].length) (baseStart_5770360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770360 prefixEnd_5770360 := by exact prefixLift 5770360
  have htrace : WordTrace (prefixWord ++ tailWord_5770360) baseStart_5770360 baseEnd_5770360 := by
    simpa [prefixWord, tailWord_5770360, baseEnd_5770360] using wordTrace_append hprefix tailTrace_5770360
  have hstable : (prefixWord ++ tailWord_5770360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770360).length < 2 ^ (prefixWord ++ tailWord_5770360).sum := by decide
  have hdescent : baseEnd_5770360 < baseStart_5770360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770387 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 3]
def baseStart_5770387 : Nat := 118140960795 + 5770387 * 2 ^ 59
def prefixEnd_5770387 : Nat := 4983230072969 + 3 ^ 40 * 5770387 * 2
def baseEnd_5770387 : Nat := 2962982093455820068024979

theorem tailTrace_5770387 : CollatzResearch.WordTrace tailWord_5770387 prefixEnd_5770387 2962982093455820068024979 := by
  unfold tailWord_5770387
  simp only [CollatzResearch.WordTrace]
  refine ⟨210463304145880877484757415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140308869430587251656504943 210463304145880877484757415)
  ·
    refine ⟨315694956218821316227136123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210463304145880877484757415 315694956218821316227136123)
    ·
      refine ⟨473542434328231974340704185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315694956218821316227136123 473542434328231974340704185)
      ·
        refine ⟨355156825746173980755528139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473542434328231974340704185 355156825746173980755528139)
        ·
          refine ⟨532735238619260971133292209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355156825746173980755528139 532735238619260971133292209)
          ·
            refine ⟨399551428964445728349969157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532735238619260971133292209 399551428964445728349969157)
            ·
              refine ⟨74915892930833574065619217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399551428964445728349969157 74915892930833574065619217)
              ·
                refine ⟨56186919698125180549214413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74915892930833574065619217 56186919698125180549214413)
                ·
                  refine ⟨21070094886796942705955405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56186919698125180549214413 21070094886796942705955405)
                  ·
                    refine ⟨7901285582548853514733277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21070094886796942705955405 7901285582548853514733277)
                    ·
                      refine ⟨2962982093455820068024979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7901285582548853514733277 2962982093455820068024979)
                      ·
                        rfl

theorem cell23_5770387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_5770387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770387 prefixEnd_5770387 := by exact prefixLift 5770387
  have htrace : WordTrace (prefixWord ++ tailWord_5770387) baseStart_5770387 baseEnd_5770387 := by
    simpa [prefixWord, tailWord_5770387, baseEnd_5770387] using wordTrace_append hprefix tailTrace_5770387
  have hstable : (prefixWord ++ tailWord_5770387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770387).length < 2 ^ (prefixWord ++ tailWord_5770387).sum := by decide
  have hdescent : baseEnd_5770387 < baseStart_5770387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770431 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 1, 3, 2]
def baseStart_5770431 : Nat := 118140960795 + 5770431 * 2 ^ 59
def prefixEnd_5770431 : Nat := 4983230072969 + 3 ^ 40 * 5770431 * 2
def baseEnd_5770431 : Nat := 2963004686604617895874777

theorem tailTrace_5770431 : CollatzResearch.WordTrace tailWord_5770431 prefixEnd_5770431 2963004686604617895874777 := by
  unfold tailWord_5770431
  simp only [CollatzResearch.WordTrace]
  refine ⟨210464908957721472999359147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140309939305147648666239431 210464908957721472999359147)
  ·
    refine ⟨315697363436582209499038721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210464908957721472999359147 315697363436582209499038721)
    ·
      refine ⟨236773022577436657124279041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315697363436582209499038721 236773022577436657124279041)
      ·
        refine ⟨177579766933077492843209281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236773022577436657124279041 177579766933077492843209281)
        ·
          refine ⟨133184825199808119632406961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177579766933077492843209281 133184825199808119632406961)
          ·
            refine ⟨99888618899856089724305221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133184825199808119632406961 99888618899856089724305221)
            ·
              refine ⟨18729116043723016823307229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99888618899856089724305221 18729116043723016823307229)
              ·
                refine ⟨7023418516396131308740211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18729116043723016823307229 7023418516396131308740211)
                ·
                  refine ⟨10535127774594196963110317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7023418516396131308740211 10535127774594196963110317)
                  ·
                    refine ⟨3950672915472823861166369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10535127774594196963110317 3950672915472823861166369)
                    ·
                      refine ⟨2963004686604617895874777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3950672915472823861166369 2963004686604617895874777)
                      ·
                        rfl

theorem cell23_5770431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_5770431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770431 prefixEnd_5770431 := by exact prefixLift 5770431
  have htrace : WordTrace (prefixWord ++ tailWord_5770431) baseStart_5770431 baseEnd_5770431 := by
    simpa [prefixWord, tailWord_5770431, baseEnd_5770431] using wordTrace_append hprefix tailTrace_5770431
  have hstable : (prefixWord ++ tailWord_5770431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770431).length < 2 ^ (prefixWord ++ tailWord_5770431).sum := by decide
  have hdescent : baseEnd_5770431 < baseStart_5770431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770457 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_5770457 : Nat := 118140960795 + 5770457 * 2 ^ 59
def prefixEnd_5770457 : Nat := 4983230072969 + 3 ^ 40 * 5770457 * 2
def baseEnd_5770457 : Nat := 2963018037101634794149657

theorem tailTrace_5770457 : CollatzResearch.WordTrace tailWord_5770457 prefixEnd_5770457 2963018037101634794149657 := by
  unfold tailWord_5770457
  simp only [CollatzResearch.WordTrace]
  refine ⟨210465857255627279439805625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140310571503751519626537083 210465857255627279439805625)
  ·
    refine ⟨157849392941720459579854219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210465857255627279439805625 157849392941720459579854219)
    ·
      refine ⟨236774089412580689369781329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157849392941720459579854219 236774089412580689369781329)
      ·
        refine ⟨177580567059435517027335997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236774089412580689369781329 177580567059435517027335997)
        ·
          refine ⟨66592712647288318885250999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177580567059435517027335997 66592712647288318885250999)
          ·
            refine ⟨99889068970932478327876499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66592712647288318885250999 99889068970932478327876499)
            ·
              refine ⟨149833603456398717491814749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99889068970932478327876499 149833603456398717491814749)
              ·
                refine ⟨56187601296149519059430531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149833603456398717491814749 56187601296149519059430531)
                ·
                  refine ⟨84281401944224278589145797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56187601296149519059430531 84281401944224278589145797)
                  ·
                    refine ⟨15802762864542052235464837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84281401944224278589145797 15802762864542052235464837)
                    ·
                      refine ⟨2963018037101634794149657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15802762864542052235464837 2963018037101634794149657)
                      ·
                        rfl

theorem cell23_5770457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_5770457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770457 prefixEnd_5770457 := by exact prefixLift 5770457
  have htrace : WordTrace (prefixWord ++ tailWord_5770457) baseStart_5770457 baseEnd_5770457 := by
    simpa [prefixWord, tailWord_5770457, baseEnd_5770457] using wordTrace_append hprefix tailTrace_5770457
  have hstable : (prefixWord ++ tailWord_5770457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770457).length < 2 ^ (prefixWord ++ tailWord_5770457).sum := by decide
  have hdescent : baseEnd_5770457 < baseStart_5770457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770531 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 2, 5]
def baseStart_5770531 : Nat := 118140960795 + 5770531 * 2 ^ 59
def prefixEnd_5770531 : Nat := 4983230072969 + 3 ^ 40 * 5770531 * 2
def baseEnd_5770531 : Nat := 987685344890022501541439

theorem tailTrace_5770531 : CollatzResearch.WordTrace tailWord_5770531 prefixEnd_5770531 987685344890022501541439 := by
  unfold tailWord_5770531
  simp only [CollatzResearch.WordTrace]
  refine ⟨210468556257359190077999447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140312370838239460051999631 210468556257359190077999447)
  ·
    refine ⟨315702834386038785116999171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210468556257359190077999447 315702834386038785116999171)
    ·
      refine ⟨473554251579058177675498757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315702834386038785116999171 473554251579058177675498757)
      ·
        refine ⟨88791422171073408314156017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 473554251579058177675498757 88791422171073408314156017)
        ·
          refine ⟨66593566628305056235617013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88791422171073408314156017 66593566628305056235617013)
          ·
            refine ⟨6243146871403599022089095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66593566628305056235617013 6243146871403599022089095)
            ·
              refine ⟨9364720307105398533133643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243146871403599022089095 9364720307105398533133643)
              ·
                refine ⟨14047080460658097799700465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9364720307105398533133643 14047080460658097799700465)
                ·
                  refine ⟨10535310345493573349775349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14047080460658097799700465 10535310345493573349775349)
                  ·
                    refine ⟨987685344890022501541439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10535310345493573349775349 987685344890022501541439)
                    ·
                      rfl

theorem cell23_5770531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 5].length) (baseStart_5770531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770531 prefixEnd_5770531 := by exact prefixLift 5770531
  have htrace : WordTrace (prefixWord ++ tailWord_5770531) baseStart_5770531 baseEnd_5770531 := by
    simpa [prefixWord, tailWord_5770531, baseEnd_5770531] using wordTrace_append hprefix tailTrace_5770531
  have hstable : (prefixWord ++ tailWord_5770531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770531).length < 2 ^ (prefixWord ++ tailWord_5770531).sum := by decide
  have hdescent : baseEnd_5770531 < baseStart_5770531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770537 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_5770537 : Nat := 118140960795 + 5770537 * 2 ^ 59
def prefixEnd_5770537 : Nat := 4983230072969 + 3 ^ 40 * 5770537 * 2
def baseEnd_5770537 : Nat := 2963059115553994481149289

theorem tailTrace_5770537 : CollatzResearch.WordTrace tailWord_5770537 prefixEnd_5770537 2963059115553994481149289 := by
  unfold tailWord_5770537
  simp only [CollatzResearch.WordTrace]
  refine ⟨210468775095337453102717865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140312516730224968735145243 210468775095337453102717865)
  ·
    refine ⟨157851581321503089827038399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210468775095337453102717865 157851581321503089827038399)
    ·
      refine ⟨236777371982254634740557599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157851581321503089827038399 236777371982254634740557599)
      ·
        refine ⟨355166057973381952110836399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236777371982254634740557599 355166057973381952110836399)
        ·
          refine ⟨532749086960072928166254599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355166057973381952110836399 532749086960072928166254599)
          ·
            refine ⟨799123630440109392249381899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532749086960072928166254599 799123630440109392249381899)
            ·
              refine ⟨1198685445660164088374072849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799123630440109392249381899 1198685445660164088374072849)
              ·
                refine ⟨899014084245123066280554637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198685445660164088374072849 899014084245123066280554637)
                ·
                  refine ⟨337130281591921149855207989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899014084245123066280554637 337130281591921149855207989)
                  ·
                    refine ⟨31605963899242607798925749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 337130281591921149855207989 31605963899242607798925749)
                    ·
                      refine ⟨2963059115553994481149289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31605963899242607798925749 2963059115553994481149289)
                      ·
                        rfl

theorem cell23_5770537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_5770537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770537 prefixEnd_5770537 := by exact prefixLift 5770537
  have htrace : WordTrace (prefixWord ++ tailWord_5770537) baseStart_5770537 baseEnd_5770537 := by
    simpa [prefixWord, tailWord_5770537, baseEnd_5770537] using wordTrace_append hprefix tailTrace_5770537
  have hstable : (prefixWord ++ tailWord_5770537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770537).length < 2 ^ (prefixWord ++ tailWord_5770537).sum := by decide
  have hdescent : baseEnd_5770537 < baseStart_5770537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770544 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 5, 4]
def baseStart_5770544 : Nat := 118140960795 + 5770544 * 2 ^ 59
def prefixEnd_5770544 : Nat := 4983230072969 + 3 ^ 40 * 5770544 * 2
def baseEnd_5770544 : Nat := 987687569972858651253919

theorem tailTrace_5770544 : CollatzResearch.WordTrace tailWord_5770544 prefixEnd_5770544 987687569972858651253919 := by
  unfold tailWord_5770544
  simp only [CollatzResearch.WordTrace]
  refine ⟨105234515203156046649111343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140312686937541395532148457 105234515203156046649111343)
  ·
    refine ⟨157851772804734069973667015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105234515203156046649111343 157851772804734069973667015)
    ·
      refine ⟨236777659207101104960500523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157851772804734069973667015 236777659207101104960500523)
      ·
        refine ⟨355166488810651657440750785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236777659207101104960500523 355166488810651657440750785)
        ·
          refine ⟨266374866607988743080563089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355166488810651657440750785 266374866607988743080563089)
          ·
            refine ⟨199781149955991557310422317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266374866607988743080563089 199781149955991557310422317)
            ·
              refine ⟨74917931233496833991408369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199781149955991557310422317 74917931233496833991408369)
              ·
                refine ⟨56188448425122625493556277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74917931233496833991408369 56188448425122625493556277)
                ·
                  refine ⟨5267667039855246140020901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56188448425122625493556277 5267667039855246140020901)
                  ·
                    refine ⟨987687569972858651253919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5267667039855246140020901 987687569972858651253919)
                    ·
                      rfl

theorem cell23_5770544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 4].length) (baseStart_5770544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770544 prefixEnd_5770544 := by exact prefixLift 5770544
  have htrace : WordTrace (prefixWord ++ tailWord_5770544) baseStart_5770544 baseEnd_5770544 := by
    simpa [prefixWord, tailWord_5770544, baseEnd_5770544] using wordTrace_append hprefix tailTrace_5770544
  have hstable : (prefixWord ++ tailWord_5770544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770544).length < 2 ^ (prefixWord ++ tailWord_5770544).sum := by decide
  have hdescent : baseEnd_5770544 < baseStart_5770544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770584 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_5770584 : Nat := 118140960795 + 5770584 * 2 ^ 59
def prefixEnd_5770584 : Nat := 4983230072969 + 3 ^ 40 * 5770584 * 2
def baseEnd_5770584 : Nat := 2963083249144755797261573

theorem tailTrace_5770584 : CollatzResearch.WordTrace tailWord_5770584 prefixEnd_5770584 2963083249144755797261573 := by
  unfold tailWord_5770584
  simp only [CollatzResearch.WordTrace]
  refine ⟨105235244663083590064839403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140313659550778120086452537 105235244663083590064839403)
  ·
    refine ⟨157852866994625385097259105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105235244663083590064839403 157852866994625385097259105)
    ·
      refine ⟨118389650245969038822944329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157852866994625385097259105 118389650245969038822944329)
      ·
        refine ⟨88792237684476779117208247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118389650245969038822944329 88792237684476779117208247)
        ·
          refine ⟨133188356526715168675812371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88792237684476779117208247 133188356526715168675812371)
          ·
            refine ⟨199782534790072753013718557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133188356526715168675812371 199782534790072753013718557)
            ·
              refine ⟨74918450546277282380144459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199782534790072753013718557 74918450546277282380144459)
              ·
                refine ⟨112377675819415923570216689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74918450546277282380144459 112377675819415923570216689)
                ·
                  refine ⟨84283256864561942677662517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112377675819415923570216689 84283256864561942677662517)
                  ·
                    refine ⟨7901555331052682126030861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84283256864561942677662517 7901555331052682126030861)
                    ·
                      refine ⟨2963083249144755797261573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7901555331052682126030861 2963083249144755797261573)
                      ·
                        rfl

theorem cell23_5770584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_5770584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770584 prefixEnd_5770584 := by exact prefixLift 5770584
  have htrace : WordTrace (prefixWord ++ tailWord_5770584) baseStart_5770584 baseEnd_5770584 := by
    simpa [prefixWord, tailWord_5770584, baseEnd_5770584] using wordTrace_append hprefix tailTrace_5770584
  have hstable : (prefixWord ++ tailWord_5770584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770584).length < 2 ^ (prefixWord ++ tailWord_5770584).sum := by decide
  have hdescent : baseEnd_5770584 < baseStart_5770584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770595 : List Nat := [1, 1, 1, 5, 2, 4, 1, 3, 1, 4]
def baseStart_5770595 : Nat := 118140960795 + 5770595 * 2 ^ 59
def prefixEnd_5770595 : Nat := 4983230072969 + 3 ^ 40 * 5770595 * 2
def baseEnd_5770595 : Nat := 987696299143985084741341

theorem tailTrace_5770595 : CollatzResearch.WordTrace tailWord_5770595 prefixEnd_5770595 987696299143985084741341 := by
  unfold tailWord_5770595
  simp only [CollatzResearch.WordTrace]
  refine ⟨210470890529127329008329239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140313927019418219338886159 210470890529127329008329239)
  ·
    refine ⟨315706335793690993512493859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210470890529127329008329239 315706335793690993512493859)
    ·
      refine ⟨473559503690536490268740789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315706335793690993512493859 473559503690536490268740789)
      ·
        refine ⟨44396203470987795962694449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 473559503690536490268740789 44396203470987795962694449)
        ·
          refine ⟨33297152603240846972020837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44396203470987795962694449 33297152603240846972020837)
          ·
            refine ⟨6243216113107658807253907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33297152603240846972020837 6243216113107658807253907)
            ·
              refine ⟨9364824169661488210880861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243216113107658807253907 9364824169661488210880861)
              ·
                refine ⟨3511809063623058079080323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9364824169661488210880861 3511809063623058079080323)
                ·
                  refine ⟨5267713595434587118620485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511809063623058079080323 5267713595434587118620485)
                  ·
                    refine ⟨987696299143985084741341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5267713595434587118620485 987696299143985084741341)
                    ·
                      rfl

theorem cell23_5770595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 4].length) (baseStart_5770595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770595 prefixEnd_5770595 := by exact prefixLift 5770595
  have htrace : WordTrace (prefixWord ++ tailWord_5770595) baseStart_5770595 baseEnd_5770595 := by
    simpa [prefixWord, tailWord_5770595, baseEnd_5770595] using wordTrace_append hprefix tailTrace_5770595
  have hstable : (prefixWord ++ tailWord_5770595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770595).length < 2 ^ (prefixWord ++ tailWord_5770595).sum := by decide
  have hdescent : baseEnd_5770595 < baseStart_5770595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770625 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 6]
def baseStart_5770625 : Nat := 118140960795 + 5770625 * 2 ^ 59
def prefixEnd_5770625 : Nat := 4983230072969 + 3 ^ 40 * 5770625 * 2
def baseEnd_5770625 : Nat := 329233811316843348538765

theorem tailTrace_5770625 : CollatzResearch.WordTrace tailWord_5770625 prefixEnd_5770625 329233811316843348538765 := by
  unfold tailWord_5770625
  simp only [CollatzResearch.WordTrace]
  refine ⟨210471984719018644131921329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140314656479345762754614219 210471984719018644131921329)
  ·
    refine ⟨157853988539263983098940997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210471984719018644131921329 157853988539263983098940997)
    ·
      refine ⟨29597622851111996831051437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157853988539263983098940997 29597622851111996831051437)
      ·
        refine ⟨11099108569166998811644289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29597622851111996831051437 11099108569166998811644289)
        ·
          refine ⟨8324331426875249108733217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11099108569166998811644289 8324331426875249108733217)
          ·
            refine ⟨6243248570156436831549913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8324331426875249108733217 6243248570156436831549913)
            ·
              refine ⟨4682436427617327623662435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6243248570156436831549913 4682436427617327623662435)
              ·
                refine ⟨7023654641425991435493653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4682436427617327623662435 7023654641425991435493653)
                ·
                  refine ⟨329233811316843348538765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7023654641425991435493653 329233811316843348538765)
                  ·
                    rfl

theorem cell23_5770625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 6].length) (baseStart_5770625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770625 prefixEnd_5770625 := by exact prefixLift 5770625
  have htrace : WordTrace (prefixWord ++ tailWord_5770625) baseStart_5770625 baseEnd_5770625 := by
    simpa [prefixWord, tailWord_5770625, baseEnd_5770625] using wordTrace_append hprefix tailTrace_5770625
  have hstable : (prefixWord ++ tailWord_5770625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770625).length < 2 ^ (prefixWord ++ tailWord_5770625).sum := by decide
  have hdescent : baseEnd_5770625 < baseStart_5770625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770638 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_5770638 : Nat := 118140960795 + 5770638 * 2 ^ 59
def prefixEnd_5770638 : Nat := 4983230072969 + 3 ^ 40 * 5770638 * 2
def baseEnd_5770638 : Nat := 987703659033366195328775

theorem tailTrace_5770638 : CollatzResearch.WordTrace tailWord_5770638 prefixEnd_5770638 987703659033366195328775 := by
  unfold tailWord_5770638
  simp only [CollatzResearch.WordTrace]
  refine ⟨26309057358496443419018071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140314972578647698234763045 26309057358496443419018071)
  ·
    refine ⟨39463586037744665128527107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26309057358496443419018071 39463586037744665128527107)
    ·
      refine ⟨59195379056616997692790661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39463586037744665128527107 59195379056616997692790661)
      ·
        refine ⟨11099133573115687067398249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59195379056616997692790661 11099133573115687067398249)
        ·
          refine ⟨8324350179836765300548687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11099133573115687067398249 8324350179836765300548687)
          ·
            refine ⟨12486525269755147950823031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8324350179836765300548687 12486525269755147950823031)
            ·
              refine ⟨18729787904632721926234547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12486525269755147950823031 18729787904632721926234547)
              ·
                refine ⟨28094681856949082889351821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18729787904632721926234547 28094681856949082889351821)
                ·
                  refine ⟨10535505696355906083506933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28094681856949082889351821 10535505696355906083506933)
                  ·
                    refine ⟨987703659033366195328775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10535505696355906083506933 987703659033366195328775)
                    ·
                      rfl

theorem cell23_5770638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_5770638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770638 prefixEnd_5770638 := by exact prefixLift 5770638
  have htrace : WordTrace (prefixWord ++ tailWord_5770638) baseStart_5770638 baseEnd_5770638 := by
    simpa [prefixWord, tailWord_5770638, baseEnd_5770638] using wordTrace_append hprefix tailTrace_5770638
  have hstable : (prefixWord ++ tailWord_5770638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770638).length < 2 ^ (prefixWord ++ tailWord_5770638).sum := by decide
  have hdescent : baseEnd_5770638 < baseStart_5770638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770669 : List Nat := [1, 5, 2, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_5770669 : Nat := 118140960795 + 5770669 * 2 ^ 59
def prefixEnd_5770669 : Nat := 4983230072969 + 3 ^ 40 * 5770669 * 2
def baseEnd_5770669 : Nat := 2963126895000387964698683

theorem tailTrace_5770669 : CollatzResearch.WordTrace tailWord_5770669 prefixEnd_5770669 2963126895000387964698683 := by
  unfold tailWord_5770669
  simp only [CollatzResearch.WordTrace]
  refine ⟨210473589530859239646523061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140315726353906159764348707 210473589530859239646523061)
  ·
    refine ⟨19731899018518053716861537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210473589530859239646523061 19731899018518053716861537)
    ·
      refine ⟨14798924263888540287646153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19731899018518053716861537 14798924263888540287646153)
      ·
        refine ⟨11099193197916405215734615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14798924263888540287646153 11099193197916405215734615)
        ·
          refine ⟨16648789796874607823601923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11099193197916405215734615 16648789796874607823601923)
          ·
            refine ⟨24973184695311911735402885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16648789796874607823601923 24973184695311911735402885)
            ·
              refine ⟨4682472130370983450388041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24973184695311911735402885 4682472130370983450388041)
              ·
                refine ⟨3511854097778237587791031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4682472130370983450388041 3511854097778237587791031)
                ·
                  refine ⟨5267781146667356381686547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511854097778237587791031 5267781146667356381686547)
                  ·
                    refine ⟨7901671720001034572529821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5267781146667356381686547 7901671720001034572529821)
                    ·
                      refine ⟨2963126895000387964698683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7901671720001034572529821 2963126895000387964698683)
                      ·
                        rfl

theorem cell23_5770669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_5770669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770669 prefixEnd_5770669 := by exact prefixLift 5770669
  have htrace : WordTrace (prefixWord ++ tailWord_5770669) baseStart_5770669 baseEnd_5770669 := by
    simpa [prefixWord, tailWord_5770669, baseEnd_5770669] using wordTrace_append hprefix tailTrace_5770669
  have hstable : (prefixWord ++ tailWord_5770669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770669).length < 2 ^ (prefixWord ++ tailWord_5770669).sum := by decide
  have hdescent : baseEnd_5770669 < baseStart_5770669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770674 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_5770674 : Nat := 118140960795 + 5770674 * 2 ^ 59
def prefixEnd_5770674 : Nat := 4983230072969 + 3 ^ 40 * 5770674 * 2
def baseEnd_5770674 : Nat := 2963129462403660445136159

theorem tailTrace_5770674 : CollatzResearch.WordTrace tailWord_5770674 prefixEnd_5770674 2963129462403660445136159 := by
  unfold tailWord_5770674
  simp only [CollatzResearch.WordTrace]
  refine ⟨52618442973960281375113769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140315847930560750333636717 52618442973960281375113769)
  ·
    refine ⟨39463832230470211031335327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52618442973960281375113769 39463832230470211031335327)
    ·
      refine ⟨59195748345705316547002991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39463832230470211031335327 59195748345705316547002991)
      ·
        refine ⟨88793622518557974820504487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59195748345705316547002991 88793622518557974820504487)
        ·
          refine ⟨133190433777836962230756731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88793622518557974820504487 133190433777836962230756731)
          ·
            refine ⟨199785650666755443346135097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133190433777836962230756731 199785650666755443346135097)
            ·
              refine ⟨149839238000066582509601323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199785650666755443346135097 149839238000066582509601323)
              ·
                refine ⟨224758857000099873764401985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149839238000066582509601323 224758857000099873764401985)
                ·
                  refine ⟨168569142750074905323301489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224758857000099873764401985 168569142750074905323301489)
                  ·
                    refine ⟨126426857062556178992476117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168569142750074905323301489 126426857062556178992476117)
                    ·
                      refine ⟨2963129462403660445136159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126426857062556178992476117 2963129462403660445136159)
                      ·
                        rfl

theorem cell23_5770674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_5770674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770674 prefixEnd_5770674 := by exact prefixLift 5770674
  have htrace : WordTrace (prefixWord ++ tailWord_5770674) baseStart_5770674 baseEnd_5770674 := by
    simpa [prefixWord, tailWord_5770674, baseEnd_5770674] using wordTrace_append hprefix tailTrace_5770674
  have hstable : (prefixWord ++ tailWord_5770674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770674).length < 2 ^ (prefixWord ++ tailWord_5770674).sum := by decide
  have hdescent : baseEnd_5770674 < baseStart_5770674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770691 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 3]
def baseStart_5770691 : Nat := 118140960795 + 5770691 * 2 ^ 59
def prefixEnd_5770691 : Nat := 4983230072969 + 3 ^ 40 * 5770691 * 2
def baseEnd_5770691 : Nat := 2963138191574786878623581

theorem tailTrace_5770691 : CollatzResearch.WordTrace tailWord_5770691 prefixEnd_5770691 2963138191574786878623581 := by
  unfold tailWord_5770691
  simp only [CollatzResearch.WordTrace]
  refine ⟨210474391936779537403823927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140316261291186358269215951 210474391936779537403823927)
  ·
    refine ⟨315711587905169306105735891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210474391936779537403823927 315711587905169306105735891)
    ·
      refine ⟨473567381857753959158603837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315711587905169306105735891 473567381857753959158603837)
      ·
        refine ⟨177587768196657734684476439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 473567381857753959158603837 177587768196657734684476439)
        ·
          refine ⟨266381652294986602026714659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177587768196657734684476439 266381652294986602026714659)
          ·
            refine ⟨399572478442479903040071989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266381652294986602026714659 399572478442479903040071989)
            ·
              refine ⟨37459919853982490910006749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 399572478442479903040071989 37459919853982490910006749)
              ·
                refine ⟨14047469945243434091252531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37459919853982490910006749 14047469945243434091252531)
                ·
                  refine ⟨21071204917865151136878797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14047469945243434091252531 21071204917865151136878797)
                  ·
                    refine ⟨7901701844199431676329549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21071204917865151136878797 7901701844199431676329549)
                    ·
                      refine ⟨2963138191574786878623581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7901701844199431676329549 2963138191574786878623581)
                      ·
                        rfl

theorem cell23_5770691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_5770691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770691 prefixEnd_5770691 := by exact prefixLift 5770691
  have htrace : WordTrace (prefixWord ++ tailWord_5770691) baseStart_5770691 baseEnd_5770691 := by
    simpa [prefixWord, tailWord_5770691, baseEnd_5770691] using wordTrace_append hprefix tailTrace_5770691
  have hstable : (prefixWord ++ tailWord_5770691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770691).length < 2 ^ (prefixWord ++ tailWord_5770691).sum := by decide
  have hdescent : baseEnd_5770691 < baseStart_5770691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770692 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5770692 : Nat := 118140960795 + 5770692 * 2 ^ 59
def prefixEnd_5770692 : Nat := 4983230072969 + 3 ^ 40 * 5770692 * 2
def baseEnd_5770692 : Nat := 2963138705055441374711077

theorem tailTrace_5770692 : CollatzResearch.WordTrace tailWord_5770692 prefixEnd_5770692 2963138705055441374711077 := by
  unfold tailWord_5770692
  simp only [CollatzResearch.WordTrace]
  refine ⟨105237214204887957287305165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140316285606517276383073553 105237214204887957287305165)
  ·
    refine ⟨39463955326832983982739437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105237214204887957287305165 39463955326832983982739437)
    ·
      refine ⟨14798983247562368993527289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39463955326832983982739437 14798983247562368993527289)
      ·
        refine ⟨11099237435671776745145467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14798983247562368993527289 11099237435671776745145467)
        ·
          refine ⟨16648856153507665117718201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11099237435671776745145467 16648856153507665117718201)
          ·
            refine ⟨12486642115130748838288651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16648856153507665117718201 12486642115130748838288651)
            ·
              refine ⟨18729963172696123257432977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12486642115130748838288651 18729963172696123257432977)
              ·
                refine ⟨14047472379522092443074733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18729963172696123257432977 14047472379522092443074733)
                ·
                  refine ⟨5267802142320784666153025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14047472379522092443074733 5267802142320784666153025)
                  ·
                    refine ⟨3950851606740588499614769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5267802142320784666153025 3950851606740588499614769)
                    ·
                      refine ⟨2963138705055441374711077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3950851606740588499614769 2963138705055441374711077)
                      ·
                        rfl

theorem cell23_5770692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5770692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770692 prefixEnd_5770692 := by exact prefixLift 5770692
  have htrace : WordTrace (prefixWord ++ tailWord_5770692) baseStart_5770692 baseEnd_5770692 := by
    simpa [prefixWord, tailWord_5770692, baseEnd_5770692] using wordTrace_append hprefix tailTrace_5770692
  have hstable : (prefixWord ++ tailWord_5770692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770692).length < 2 ^ (prefixWord ++ tailWord_5770692).sum := by decide
  have hdescent : baseEnd_5770692 < baseStart_5770692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770704 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_5770704 : Nat := 118140960795 + 5770704 * 2 ^ 59
def prefixEnd_5770704 : Nat := 4983230072969 + 3 ^ 40 * 5770704 * 2
def baseEnd_5770704 : Nat := 2963144866823295327761021

theorem tailTrace_5770704 : CollatzResearch.WordTrace tailWord_5770704 prefixEnd_5770704 2963144866823295327761021 := by
  unfold tailWord_5770704
  simp only [CollatzResearch.WordTrace]
  refine ⟨105237433042866220312023583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140316577390488293749364777 105237433042866220312023583)
  ·
    refine ⟨157856149564299330468035375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105237433042866220312023583 157856149564299330468035375)
    ·
      refine ⟨236784224346448995702053063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157856149564299330468035375 236784224346448995702053063)
      ·
        refine ⟨355176336519673493553079595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236784224346448995702053063 355176336519673493553079595)
        ·
          refine ⟨532764504779510240329619393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355176336519673493553079595 532764504779510240329619393)
          ·
            refine ⟨399573378584632680247214545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532764504779510240329619393 399573378584632680247214545)
            ·
              refine ⟨299680033938474510185410909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399573378584632680247214545 299680033938474510185410909)
              ·
                refine ⟨112380012726927941319529091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299680033938474510185410909 112380012726927941319529091)
                ·
                  refine ⟨168570019090391911979293637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112380012726927941319529091 168570019090391911979293637)
                  ·
                    refine ⟨31606878579448483496117557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168570019090391911979293637 31606878579448483496117557)
                    ·
                      refine ⟨2963144866823295327761021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31606878579448483496117557 2963144866823295327761021)
                      ·
                        rfl

theorem cell23_5770704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_5770704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770704 prefixEnd_5770704 := by exact prefixLift 5770704
  have htrace : WordTrace (prefixWord ++ tailWord_5770704) baseStart_5770704 baseEnd_5770704 := by
    simpa [prefixWord, tailWord_5770704, baseEnd_5770704] using wordTrace_append hprefix tailTrace_5770704
  have hstable : (prefixWord ++ tailWord_5770704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770704).length < 2 ^ (prefixWord ++ tailWord_5770704).sum := by decide
  have hdescent : baseEnd_5770704 < baseStart_5770704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770725 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5770725 : Nat := 118140960795 + 5770725 * 2 ^ 59
def prefixEnd_5770725 : Nat := 4983230072969 + 3 ^ 40 * 5770725 * 2
def baseEnd_5770725 : Nat := 2963155649917039745598425

theorem tailTrace_5770725 : CollatzResearch.WordTrace tailWord_5770725 prefixEnd_5770725 2963155649917039745598425 := by
  unfold tailWord_5770725
  simp only [CollatzResearch.WordTrace]
  refine ⟨210475632018656361210561629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140317088012437574140374419 210475632018656361210561629)
  ·
    refine ⟨78928362006996135453960611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210475632018656361210561629 78928362006996135453960611)
    ·
      refine ⟨118392543010494203180940917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78928362006996135453960611 118392543010494203180940917)
      ·
        refine ⟨11099300907233831548213211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118392543010494203180940917 11099300907233831548213211)
        ·
          refine ⟨16648951360850747322319817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11099300907233831548213211 16648951360850747322319817)
          ·
            refine ⟨12486713520638060491739863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16648951360850747322319817 12486713520638060491739863)
            ·
              refine ⟨18730070280957090737609795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12486713520638060491739863 18730070280957090737609795)
              ·
                refine ⟨28095105421435636106414693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18730070280957090737609795 28095105421435636106414693)
                ·
                  refine ⟨5267832266519181769952755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28095105421435636106414693 5267832266519181769952755)
                  ·
                    refine ⟨7901748399778772654929133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5267832266519181769952755 7901748399778772654929133)
                    ·
                      refine ⟨2963155649917039745598425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7901748399778772654929133 2963155649917039745598425)
                      ·
                        rfl

theorem cell23_5770725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5770725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770725 prefixEnd_5770725 := by exact prefixLift 5770725
  have htrace : WordTrace (prefixWord ++ tailWord_5770725) baseStart_5770725 baseEnd_5770725 := by
    simpa [prefixWord, tailWord_5770725, baseEnd_5770725] using wordTrace_append hprefix tailTrace_5770725
  have hstable : (prefixWord ++ tailWord_5770725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770725).length < 2 ^ (prefixWord ++ tailWord_5770725).sum := by decide
  have hdescent : baseEnd_5770725 < baseStart_5770725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770781 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_5770781 : Nat := 118140960795 + 5770781 * 2 ^ 59
def prefixEnd_5770781 : Nat := 4983230072969 + 3 ^ 40 * 5770781 * 2
def baseEnd_5770781 : Nat := 2963184404833691526498167

theorem tailTrace_5770781 : CollatzResearch.WordTrace tailWord_5770781 prefixEnd_5770781 2963184404833691526498167 := by
  unfold tailWord_5770781
  simp only [CollatzResearch.WordTrace]
  refine ⟨210477674506453482774600197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140318449670968988516400131 210477674506453482774600197)
  ·
    refine ⟨39464563969960028020237537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210477674506453482774600197 39464563969960028020237537)
    ·
      refine ⟨29598422977470021015178153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39464563969960028020237537 29598422977470021015178153)
      ·
        refine ⟨22198817233102515761383615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29598422977470021015178153 22198817233102515761383615)
        ·
          refine ⟨33298225849653773642075423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22198817233102515761383615 33298225849653773642075423)
          ·
            refine ⟨49947338774480660463113135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33298225849653773642075423 49947338774480660463113135)
            ·
              refine ⟨74921008161720990694669703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49947338774480660463113135 74921008161720990694669703)
              ·
                refine ⟨112381512242581486042004555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74921008161720990694669703 112381512242581486042004555)
                ·
                  refine ⟨168572268363872229063006833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112381512242581486042004555 168572268363872229063006833)
                  ·
                    refine ⟨126429201272904171797255125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168572268363872229063006833 126429201272904171797255125)
                    ·
                      refine ⟨2963184404833691526498167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126429201272904171797255125 2963184404833691526498167)
                      ·
                        rfl

theorem cell23_5770781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_5770781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770781 prefixEnd_5770781 := by exact prefixLift 5770781
  have htrace : WordTrace (prefixWord ++ tailWord_5770781) baseStart_5770781 baseEnd_5770781 := by
    simpa [prefixWord, tailWord_5770781, baseEnd_5770781] using wordTrace_append hprefix tailTrace_5770781
  have hstable : (prefixWord ++ tailWord_5770781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770781).length < 2 ^ (prefixWord ++ tailWord_5770781).sum := by decide
  have hdescent : baseEnd_5770781 < baseStart_5770781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770801 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 6, 5]
def baseStart_5770801 : Nat := 118140960795 + 5770801 * 2 ^ 59
def prefixEnd_5770801 : Nat := 4983230072969 + 3 ^ 40 * 5770801 * 2
def baseEnd_5770801 : Nat := 987731558148927149416025

theorem tailTrace_5770801 : CollatzResearch.WordTrace tailWord_5770801 prefixEnd_5770801 987731558148927149416025 := by
  unfold tailWord_5770801
  simp only [CollatzResearch.WordTrace]
  refine ⟨210478403966381026190328257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140318935977587350793552171 210478403966381026190328257)
  ·
    refine ⟨157858802974785769642746193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210478403966381026190328257 157858802974785769642746193)
    ·
      refine ⟨118394102231089327232059645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157858802974785769642746193 118394102231089327232059645)
      ·
        refine ⟨44397788336658497712022367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118394102231089327232059645 44397788336658497712022367)
        ·
          refine ⟨66596682504987746568033551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44397788336658497712022367 66596682504987746568033551)
          ·
            refine ⟨99895023757481619852050327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66596682504987746568033551 99895023757481619852050327)
            ·
              refine ⟨149842535636222429778075491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99895023757481619852050327 149842535636222429778075491)
              ·
                refine ⟨224763803454333644667113237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149842535636222429778075491 224763803454333644667113237)
                ·
                  refine ⟨10535803286921889593770933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 224763803454333644667113237 10535803286921889593770933)
                  ·
                    refine ⟨987731558148927149416025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10535803286921889593770933 987731558148927149416025)
                    ·
                      rfl

theorem cell23_5770801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_5770801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770801 prefixEnd_5770801 := by exact prefixLift 5770801
  have htrace : WordTrace (prefixWord ++ tailWord_5770801) baseStart_5770801 baseEnd_5770801 := by
    simpa [prefixWord, tailWord_5770801, baseEnd_5770801] using wordTrace_append hprefix tailTrace_5770801
  have hstable : (prefixWord ++ tailWord_5770801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770801).length < 2 ^ (prefixWord ++ tailWord_5770801).sum := by decide
  have hdescent : baseEnd_5770801 < baseStart_5770801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770848 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 3, 4]
def baseStart_5770848 : Nat := 118140960795 + 5770848 * 2 ^ 59
def prefixEnd_5770848 : Nat := 4983230072969 + 3 ^ 40 * 5770848 * 2
def baseEnd_5770848 : Nat := 987739602679180921453453

theorem tailTrace_5770848 : CollatzResearch.WordTrace tailWord_5770848 prefixEnd_5770848 987739602679180921453453 := by
  unfold tailWord_5770848
  simp only [CollatzResearch.WordTrace]
  refine ⟨105240059098605376608644599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140320078798140502144859465 105240059098605376608644599)
  ·
    refine ⟨157860088647908064912966899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105240059098605376608644599 157860088647908064912966899)
    ·
      refine ⟨236790132971862097369450349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157860088647908064912966899 236790132971862097369450349)
      ·
        refine ⟨88796299864448286513543881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236790132971862097369450349 88796299864448286513543881)
        ·
          refine ⟨66597224898336214885157911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88796299864448286513543881 66597224898336214885157911)
          ·
            refine ⟨99895837347504322327736867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66597224898336214885157911 99895837347504322327736867)
            ·
              refine ⟨149843756021256483491605301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99895837347504322327736867 149843756021256483491605301)
              ·
                refine ⟨14047852126992795327337997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149843756021256483491605301 14047852126992795327337997)
                ·
                  refine ⟨5267944547622298247751749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14047852126992795327337997 5267944547622298247751749)
                  ·
                    refine ⟨987739602679180921453453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5267944547622298247751749 987739602679180921453453)
                    ·
                      rfl

theorem cell23_5770848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 4].length) (baseStart_5770848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770848 prefixEnd_5770848 := by exact prefixLift 5770848
  have htrace : WordTrace (prefixWord ++ tailWord_5770848) baseStart_5770848 baseEnd_5770848 := by
    simpa [prefixWord, tailWord_5770848, baseEnd_5770848] using wordTrace_append hprefix tailTrace_5770848
  have hstable : (prefixWord ++ tailWord_5770848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770848).length < 2 ^ (prefixWord ++ tailWord_5770848).sum := by decide
  have hdescent : baseEnd_5770848 < baseStart_5770848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770928 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_5770928 : Nat := 118140960795 + 5770928 * 2 ^ 59
def prefixEnd_5770928 : Nat := 4983230072969 + 3 ^ 40 * 5770928 * 2
def baseEnd_5770928 : Nat := 2963259886489902451359991

theorem tailTrace_5770928 : CollatzResearch.WordTrace tailWord_5770928 prefixEnd_5770928 2963259886489902451359991 := by
  unfold tailWord_5770928
  simp only [CollatzResearch.WordTrace]
  refine ⟨105241518018460463440100719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140322024024613951253467625 105241518018460463440100719)
  ·
    refine ⟨157862277027690695160151079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105241518018460463440100719 157862277027690695160151079)
    ·
      refine ⟨236793415541536042740226619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157862277027690695160151079 236793415541536042740226619)
      ·
        refine ⟨355190123312304064110339929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236793415541536042740226619 355190123312304064110339929)
        ·
          refine ⟨266392592484228048082754947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355190123312304064110339929 266392592484228048082754947)
          ·
            refine ⟨399588888726342072124132421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266392592484228048082754947 399588888726342072124132421)
            ·
              refine ⟨74922916636189138523274829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399588888726342072124132421 74922916636189138523274829)
              ·
                refine ⟨28096093738570926946228061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74922916636189138523274829 28096093738570926946228061)
                ·
                  refine ⟨10536035151964097604835523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28096093738570926946228061 10536035151964097604835523)
                  ·
                    refine ⟨15804052727946146407253285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10536035151964097604835523 15804052727946146407253285)
                    ·
                      refine ⟨2963259886489902451359991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15804052727946146407253285 2963259886489902451359991)
                      ·
                        rfl

theorem cell23_5770928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_5770928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770928 prefixEnd_5770928 := by exact prefixLift 5770928
  have htrace : WordTrace (prefixWord ++ tailWord_5770928) baseStart_5770928 baseEnd_5770928 := by
    simpa [prefixWord, tailWord_5770928, baseEnd_5770928] using wordTrace_append hprefix tailTrace_5770928
  have hstable : (prefixWord ++ tailWord_5770928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770928).length < 2 ^ (prefixWord ++ tailWord_5770928).sum := by decide
  have hdescent : baseEnd_5770928 < baseStart_5770928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770956 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5770956 : Nat := 118140960795 + 5770956 * 2 ^ 59
def prefixEnd_5770956 : Nat := 4983230072969 + 3 ^ 40 * 5770956 * 2
def baseEnd_5770956 : Nat := 2963274263948228341809863

theorem tailTrace_5770956 : CollatzResearch.WordTrace tailWord_5770956 prefixEnd_5770956 2963274263948228341809863 := by
  unfold tailWord_5770956
  simp only [CollatzResearch.WordTrace]
  refine ⟨105242028640409743831110361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140322704853879658441480481 105242028640409743831110361)
  ·
    refine ⟨78931521480307307873332771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105242028640409743831110361 78931521480307307873332771)
    ·
      refine ⟨118397282220460961809999157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78931521480307307873332771 118397282220460961809999157)
      ·
        refine ⟨11099745208168215169687421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118397282220460961809999157 11099745208168215169687421)
        ·
          refine ⟨4162404453063080688632783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11099745208168215169687421 4162404453063080688632783)
          ·
            refine ⟨6243606679594621032949175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162404453063080688632783 6243606679594621032949175)
            ·
              refine ⟨9365410019391931549423763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243606679594621032949175 9365410019391931549423763)
              ·
                refine ⟨14048115029087897324135645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9365410019391931549423763 14048115029087897324135645)
                ·
                  refine ⟨5268043135907961496550867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14048115029087897324135645 5268043135907961496550867)
                  ·
                    refine ⟨7902064703861942244826301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5268043135907961496550867 7902064703861942244826301)
                    ·
                      refine ⟨2963274263948228341809863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7902064703861942244826301 2963274263948228341809863)
                      ·
                        rfl

theorem cell23_5770956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5770956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770956 prefixEnd_5770956 := by exact prefixLift 5770956
  have htrace : WordTrace (prefixWord ++ tailWord_5770956) baseStart_5770956 baseEnd_5770956 := by
    simpa [prefixWord, tailWord_5770956, baseEnd_5770956] using wordTrace_append hprefix tailTrace_5770956
  have hstable : (prefixWord ++ tailWord_5770956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770956).length < 2 ^ (prefixWord ++ tailWord_5770956).sum := by decide
  have hdescent : baseEnd_5770956 < baseStart_5770956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770958 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_5770958 : Nat := 118140960795 + 5770958 * 2 ^ 59
def prefixEnd_5770958 : Nat := 4983230072969 + 3 ^ 40 * 5770958 * 2
def baseEnd_5770958 : Nat := 2963275290909537333984853

theorem tailTrace_5770958 : CollatzResearch.WordTrace tailWord_5770958 prefixEnd_5770958 2963275290909537333984853 := by
  unfold tailWord_5770958
  simp only [CollatzResearch.WordTrace]
  refine ⟨26310516278351530250474191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140322753484541494669195685 26310516278351530250474191)
  ·
    refine ⟨39465774417527295375711287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26310516278351530250474191 39465774417527295375711287)
    ·
      refine ⟨59198661626290943063566931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39465774417527295375711287 59198661626290943063566931)
      ·
        refine ⟨88797992439436414595350397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59198661626290943063566931 88797992439436414595350397)
        ·
          refine ⟨33299247164788655473256399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88797992439436414595350397 33299247164788655473256399)
          ·
            refine ⟨49948870747182983209884599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33299247164788655473256399 49948870747182983209884599)
            ·
              refine ⟨74923306120774474814826899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49948870747182983209884599 74923306120774474814826899)
              ·
                refine ⟨112384959181161712222240349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74923306120774474814826899 112384959181161712222240349)
                ·
                  refine ⟨42144359692935642083340131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112384959181161712222240349 42144359692935642083340131)
                  ·
                    refine ⟨63216539539403463125010197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42144359692935642083340131 63216539539403463125010197)
                    ·
                      refine ⟨2963275290909537333984853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63216539539403463125010197 2963275290909537333984853)
                      ·
                        rfl

theorem cell23_5770958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_5770958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770958 prefixEnd_5770958 := by exact prefixLift 5770958
  have htrace : WordTrace (prefixWord ++ tailWord_5770958) baseStart_5770958 baseEnd_5770958 := by
    simpa [prefixWord, tailWord_5770958, baseEnd_5770958] using wordTrace_append hprefix tailTrace_5770958
  have hstable : (prefixWord ++ tailWord_5770958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770958).length < 2 ^ (prefixWord ++ tailWord_5770958).sum := by decide
  have hdescent : baseEnd_5770958 < baseStart_5770958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770968 : List Nat := [2, 1, 2, 2, 3, 1, 4, 8]
def baseStart_5770968 : Nat := 118140960795 + 5770968 * 2 ^ 59
def prefixEnd_5770968 : Nat := 4983230072969 + 3 ^ 40 * 5770968 * 2
def baseEnd_5770968 : Nat := 109751126878373418328141

theorem tailTrace_5770968 : CollatzResearch.WordTrace tailWord_5770968 prefixEnd_5770968 109751126878373418328141 := by
  unfold tailWord_5770968
  simp only [CollatzResearch.WordTrace]
  refine ⟨105242247478388006855828779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140322996637850675807771705 105242247478388006855828779)
  ·
    refine ⟨157863371217582010283743169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105242247478388006855828779 157863371217582010283743169)
    ·
      refine ⟨118397528413186507712807377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157863371217582010283743169 118397528413186507712807377)
      ·
        refine ⟨88798146309889880784605533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118397528413186507712807377 88798146309889880784605533)
        ·
          refine ⟨33299304866208705294227075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88798146309889880784605533 33299304866208705294227075)
          ·
            refine ⟨49948957299313057941340613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33299304866208705294227075 49948957299313057941340613)
            ·
              refine ⟨9365429493621198364001365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49948957299313057941340613 9365429493621198364001365)
              ·
                refine ⟨109751126878373418328141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9365429493621198364001365 109751126878373418328141)
                ·
                  rfl

theorem cell23_5770968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 8].length) (baseStart_5770968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770968 prefixEnd_5770968 := by exact prefixLift 5770968
  have htrace : WordTrace (prefixWord ++ tailWord_5770968) baseStart_5770968 baseEnd_5770968 := by
    simpa [prefixWord, tailWord_5770968, baseEnd_5770968] using wordTrace_append hprefix tailTrace_5770968
  have hstable : (prefixWord ++ tailWord_5770968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770968).length < 2 ^ (prefixWord ++ tailWord_5770968).sum := by decide
  have hdescent : baseEnd_5770968 < baseStart_5770968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770979 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5770979 : Nat := 118140960795 + 5770979 * 2 ^ 59
def prefixEnd_5770979 : Nat := 4983230072969 + 3 ^ 40 * 5770979 * 2
def baseEnd_5770979 : Nat := 2963286074003281751822257

theorem tailTrace_5770979 : CollatzResearch.WordTrace tailWord_5770979 prefixEnd_5770979 2963286074003281751822257 := by
  unfold tailWord_5770979
  simp only [CollatzResearch.WordTrace]
  refine ⟨210484896159736162590307991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140323264106490775060205327 210484896159736162590307991)
  ·
    refine ⟨315727344239604243885461987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210484896159736162590307991 315727344239604243885461987)
    ·
      refine ⟨473591016359406365828192981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315727344239604243885461987 473591016359406365828192981)
      ·
        refine ⟨11099789445923586699098273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 473591016359406365828192981 11099789445923586699098273)
        ·
          refine ⟨8324842084442690024323705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11099789445923586699098273 8324842084442690024323705)
          ·
            refine ⟨6243631563332017518242779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8324842084442690024323705 6243631563332017518242779)
            ·
              refine ⟨9365447344998026277364169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243631563332017518242779 9365447344998026277364169)
              ·
                refine ⟨7024085508748519708023127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9365447344998026277364169 7024085508748519708023127)
                ·
                  refine ⟨10536128263122779562034691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7024085508748519708023127 10536128263122779562034691)
                  ·
                    refine ⟨15804192394684169343052037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10536128263122779562034691 15804192394684169343052037)
                    ·
                      refine ⟨2963286074003281751822257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15804192394684169343052037 2963286074003281751822257)
                      ·
                        rfl

theorem cell23_5770979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5770979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770979 prefixEnd_5770979 := by exact prefixLift 5770979
  have htrace : WordTrace (prefixWord ++ tailWord_5770979) baseStart_5770979 baseEnd_5770979 := by
    simpa [prefixWord, tailWord_5770979, baseEnd_5770979] using wordTrace_append hprefix tailTrace_5770979
  have hstable : (prefixWord ++ tailWord_5770979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770979).length < 2 ^ (prefixWord ++ tailWord_5770979).sum := by decide
  have hdescent : baseEnd_5770979 < baseStart_5770979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5770995 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 3]
def baseStart_5770995 : Nat := 118140960795 + 5770995 * 2 ^ 59
def prefixEnd_5770995 : Nat := 4983230072969 + 3 ^ 40 * 5770995 * 2
def baseEnd_5770995 : Nat := 2963294289693753689222183

theorem tailTrace_5770995 : CollatzResearch.WordTrace tailWord_5770995 prefixEnd_5770995 2963294289693753689222183 := by
  unfold tailWord_5770995
  simp only [CollatzResearch.WordTrace]
  refine ⟨210485479727678197322890439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140323653151785464881926959 210485479727678197322890439)
  ·
    refine ⟨315728219591517295984335659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210485479727678197322890439 315728219591517295984335659)
    ·
      refine ⟨473592329387275943976503489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315728219591517295984335659 473592329387275943976503489)
      ·
        refine ⟨355194247040456957982377617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473592329387275943976503489 355194247040456957982377617)
        ·
          refine ⟨266395685280342718486783213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355194247040456957982377617 266395685280342718486783213)
          ·
            refine ⟨99898381980128519432543705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266395685280342718486783213 99898381980128519432543705)
            ·
              refine ⟨74923786485096389574407779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99898381980128519432543705 74923786485096389574407779)
              ·
                refine ⟨112385679727644584361611669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74923786485096389574407779 112385679727644584361611669)
                ·
                  refine ⟨5268078737233339891950547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112385679727644584361611669 5268078737233339891950547)
                  ·
                    refine ⟨7902118105850009837925821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5268078737233339891950547 7902118105850009837925821)
                    ·
                      refine ⟨2963294289693753689222183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7902118105850009837925821 2963294289693753689222183)
                      ·
                        rfl

theorem cell23_5770995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 3].length) (baseStart_5770995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5770995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5770995 prefixEnd_5770995 := by exact prefixLift 5770995
  have htrace : WordTrace (prefixWord ++ tailWord_5770995) baseStart_5770995 baseEnd_5770995 := by
    simpa [prefixWord, tailWord_5770995, baseEnd_5770995] using wordTrace_append hprefix tailTrace_5770995
  have hstable : (prefixWord ++ tailWord_5770995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5770995).length < 2 ^ (prefixWord ++ tailWord_5770995).sum := by decide
  have hdescent : baseEnd_5770995 < baseStart_5770995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5770995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771022 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_5771022 : Nat := 118140960795 + 5771022 * 2 ^ 59
def prefixEnd_5771022 : Nat := 4983230072969 + 3 ^ 40 * 5771022 * 2
def baseEnd_5771022 : Nat := 2963308153671425083584559

theorem tailTrace_5771022 : CollatzResearch.WordTrace tailWord_5771022 prefixEnd_5771022 2963308153671425083584559 := by
  unfold tailWord_5771022
  simp only [CollatzResearch.WordTrace]
  refine ⟨26310808062322547616765415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140324309665720253956082213 26310808062322547616765415)
  ·
    refine ⟨39466212093483821425148123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26310808062322547616765415 39466212093483821425148123)
    ·
      refine ⟨59199318140225732137722185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39466212093483821425148123 59199318140225732137722185)
      ·
        refine ⟨44399488605169299103291639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59199318140225732137722185 44399488605169299103291639)
        ·
          refine ⟨66599232907753948654937459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44399488605169299103291639 66599232907753948654937459)
          ·
            refine ⟨99898849361630922982406189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66599232907753948654937459 99898849361630922982406189)
            ·
              refine ⟨37462068510611596118402321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99898849361630922982406189 37462068510611596118402321)
              ·
                refine ⟨28096551382958697088801741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37462068510611596118402321 28096551382958697088801741)
                ·
                  refine ⟨10536206768609511408300653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28096551382958697088801741 10536206768609511408300653)
                  ·
                    refine ⟨3951077538228566778112745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10536206768609511408300653 3951077538228566778112745)
                    ·
                      refine ⟨2963308153671425083584559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951077538228566778112745 2963308153671425083584559)
                      ·
                        rfl

theorem cell23_5771022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_5771022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771022 prefixEnd_5771022 := by exact prefixLift 5771022
  have htrace : WordTrace (prefixWord ++ tailWord_5771022) baseStart_5771022 baseEnd_5771022 := by
    simpa [prefixWord, tailWord_5771022, baseEnd_5771022] using wordTrace_append hprefix tailTrace_5771022
  have hstable : (prefixWord ++ tailWord_5771022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771022).length < 2 ^ (prefixWord ++ tailWord_5771022).sum := by decide
  have hdescent : baseEnd_5771022 < baseStart_5771022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771035 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 5, 4, 2]
def baseStart_5771035 : Nat := 118140960795 + 5771035 * 2 ^ 59
def prefixEnd_5771035 : Nat := 4983230072969 + 3 ^ 40 * 5771035 * 2
def baseEnd_5771035 : Nat := 2963314828919933532721999

theorem tailTrace_5771035 : CollatzResearch.WordTrace tailWord_5771035 prefixEnd_5771035 2963314828919933532721999 := by
  unfold tailWord_5771035
  simp only [CollatzResearch.WordTrace]
  refine ⟨210486938647533284154346559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140324625765022189436231039 210486938647533284154346559)
  ·
    refine ⟨315730407971299926231519839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210486938647533284154346559 315730407971299926231519839)
    ·
      refine ⟨473595611956949889347279759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315730407971299926231519839 473595611956949889347279759)
      ·
        refine ⟨710393417935424834020919639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473595611956949889347279759 710393417935424834020919639)
        ·
          refine ⟨1065590126903137251031379459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710393417935424834020919639 1065590126903137251031379459)
          ·
            refine ⟨1598385190354705876547069189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065590126903137251031379459 1598385190354705876547069189)
            ·
              refine ⟨299697223191507351852575473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1598385190354705876547069189 299697223191507351852575473)
              ·
                refine ⟨224772917393630513889431605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299697223191507351852575473 224772917393630513889431605)
                ·
                  refine ⟨21072461005652860677134213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224772917393630513889431605 21072461005652860677134213)
                  ·
                    refine ⟨3951086438559911376962665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21072461005652860677134213 3951086438559911376962665)
                    ·
                      refine ⟨2963314828919933532721999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951086438559911376962665 2963314828919933532721999)
                      ·
                        rfl

theorem cell23_5771035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 4, 2].length) (baseStart_5771035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771035 prefixEnd_5771035 := by exact prefixLift 5771035
  have htrace : WordTrace (prefixWord ++ tailWord_5771035) baseStart_5771035 baseEnd_5771035 := by
    simpa [prefixWord, tailWord_5771035, baseEnd_5771035] using wordTrace_append hprefix tailTrace_5771035
  have hstable : (prefixWord ++ tailWord_5771035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771035).length < 2 ^ (prefixWord ++ tailWord_5771035).sum := by decide
  have hdescent : baseEnd_5771035 < baseStart_5771035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771052 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 1, 4, 2]
def baseStart_5771052 : Nat := 118140960795 + 5771052 * 2 ^ 59
def prefixEnd_5771052 : Nat := 4983230072969 + 3 ^ 40 * 5771052 * 2
def baseEnd_5771052 : Nat := 2963323558091059966209421

theorem tailTrace_5771052 : CollatzResearch.WordTrace tailWord_5771052 prefixEnd_5771052 2963323558091059966209421 := by
  unfold tailWord_5771052
  simp only [CollatzResearch.WordTrace]
  refine ⟨105243779344235848028857705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140325039125647797371810273 105243779344235848028857705)
  ·
    refine ⟨78932834508176886021643279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105243779344235848028857705 78932834508176886021643279)
    ·
      refine ⟨118399251762265329032464919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78932834508176886021643279 118399251762265329032464919)
      ·
        refine ⟨177598877643397993548697379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118399251762265329032464919 177598877643397993548697379)
        ·
          refine ⟨266398316465096990323046069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177598877643397993548697379 266398316465096990323046069)
          ·
            refine ⟨24974842168602842842785569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 266398316465096990323046069 24974842168602842842785569)
            ·
              refine ⟨18731131626452132132089177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24974842168602842842785569 18731131626452132132089177)
              ·
                refine ⟨14048348719839099099066883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18731131626452132132089177 14048348719839099099066883)
                ·
                  refine ⟨21072523079758648648600325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14048348719839099099066883 21072523079758648648600325)
                  ·
                    refine ⟨3951098077454746621612561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21072523079758648648600325 3951098077454746621612561)
                    ·
                      refine ⟨2963323558091059966209421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951098077454746621612561 2963323558091059966209421)
                      ·
                        rfl

theorem cell23_5771052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_5771052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771052 prefixEnd_5771052 := by exact prefixLift 5771052
  have htrace : WordTrace (prefixWord ++ tailWord_5771052) baseStart_5771052 baseEnd_5771052 := by
    simpa [prefixWord, tailWord_5771052, baseEnd_5771052] using wordTrace_append hprefix tailTrace_5771052
  have hstable : (prefixWord ++ tailWord_5771052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771052).length < 2 ^ (prefixWord ++ tailWord_5771052).sum := by decide
  have hdescent : baseEnd_5771052 < baseStart_5771052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771062 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_5771062 : Nat := 118140960795 + 5771062 * 2 ^ 59
def prefixEnd_5771062 : Nat := 4983230072969 + 3 ^ 40 * 5771062 * 2
def baseEnd_5771062 : Nat := 987776230965868309028125

theorem tailTrace_5771062 : CollatzResearch.WordTrace tailWord_5771062 prefixEnd_5771062 987776230965868309028125 := by
  unfold tailWord_5771062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13155495213652216735348715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140325282278956978510386293 13155495213652216735348715)
  ·
    refine ⟨19733242820478325103023073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13155495213652216735348715 19733242820478325103023073)
    ·
      refine ⟨14799932115358743827267305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19733242820478325103023073 14799932115358743827267305)
      ·
        refine ⟨11099949086519057870450479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14799932115358743827267305 11099949086519057870450479)
        ·
          refine ⟨16649923629778586805675719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11099949086519057870450479 16649923629778586805675719)
          ·
            refine ⟨24974885444667880208513579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16649923629778586805675719 24974885444667880208513579)
            ·
              refine ⟨37462328167001820312770369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24974885444667880208513579 37462328167001820312770369)
              ·
                refine ⟨28096746125251365234577777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37462328167001820312770369 28096746125251365234577777)
                ·
                  refine ⟨21072559593938523925933333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28096746125251365234577777 21072559593938523925933333)
                  ·
                    refine ⟨987776230965868309028125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21072559593938523925933333 987776230965868309028125)
                    ·
                      rfl

theorem cell23_5771062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_5771062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771062 prefixEnd_5771062 := by exact prefixLift 5771062
  have htrace : WordTrace (prefixWord ++ tailWord_5771062) baseStart_5771062 baseEnd_5771062 := by
    simpa [prefixWord, tailWord_5771062, baseEnd_5771062] using wordTrace_append hprefix tailTrace_5771062
  have hstable : (prefixWord ++ tailWord_5771062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771062).length < 2 ^ (prefixWord ++ tailWord_5771062).sum := by decide
  have hdescent : baseEnd_5771062 < baseStart_5771062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771075 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 7]
def baseStart_5771075 : Nat := 118140960795 + 5771075 * 2 ^ 59
def prefixEnd_5771075 : Nat := 4983230072969 + 3 ^ 40 * 5771075 * 2
def baseEnd_5771075 : Nat := 329259485349568152913535

theorem tailTrace_5771075 : CollatzResearch.WordTrace tailWord_5771075 prefixEnd_5771075 329259485349568152913535 := by
  unfold tailWord_5771075
  simp only [CollatzResearch.WordTrace]
  refine ⟨210488397567388370985802679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140325598378258913990535119 210488397567388370985802679)
  ·
    refine ⟨315732596351082556478704019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210488397567388370985802679 315732596351082556478704019)
    ·
      refine ⟨473598894526623834718056029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315732596351082556478704019 473598894526623834718056029)
      ·
        refine ⟨177599585447483938019271011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 473598894526623834718056029 177599585447483938019271011)
        ·
          refine ⟨266399378171225907028906517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177599585447483938019271011 266399378171225907028906517)
          ·
            refine ⟨12487470851776214391979993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 266399378171225907028906517 12487470851776214391979993)
            ·
              refine ⟨9365603138832160793984995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12487470851776214391979993 9365603138832160793984995)
              ·
                refine ⟨14048404708248241190977493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9365603138832160793984995 14048404708248241190977493)
                ·
                  refine ⟨329259485349568152913535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14048404708248241190977493 329259485349568152913535)
                  ·
                    rfl

theorem cell23_5771075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 7].length) (baseStart_5771075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771075 prefixEnd_5771075 := by exact prefixLift 5771075
  have htrace : WordTrace (prefixWord ++ tailWord_5771075) baseStart_5771075 baseEnd_5771075 := by
    simpa [prefixWord, tailWord_5771075, baseEnd_5771075] using wordTrace_append hprefix tailTrace_5771075
  have hstable : (prefixWord ++ tailWord_5771075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771075).length < 2 ^ (prefixWord ++ tailWord_5771075).sum := by decide
  have hdescent : baseEnd_5771075 < baseStart_5771075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771105 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 2, 5]
def baseStart_5771105 : Nat := 118140960795 + 5771105 * 2 ^ 59
def prefixEnd_5771105 : Nat := 4983230072969 + 3 ^ 40 * 5771105 * 2
def baseEnd_5771105 : Nat := 987783590855249419615559

theorem tailTrace_5771105 : CollatzResearch.WordTrace tailWord_5771105 prefixEnd_5771105 987783590855249419615559 := by
  unfold tailWord_5771105
  simp only [CollatzResearch.WordTrace]
  refine ⟨210489491757279686109394769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140326327838186457406263179 210489491757279686109394769)
  ·
    refine ⟨157867118817959764582046077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210489491757279686109394769 157867118817959764582046077)
    ·
      refine ⟨59200169556734911718267279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157867118817959764582046077 59200169556734911718267279)
      ·
        refine ⟨88800254335102367577400919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59200169556734911718267279 88800254335102367577400919)
        ·
          refine ⟨133200381502653551366101379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88800254335102367577400919 133200381502653551366101379)
          ·
            refine ⟨199800572253980327049152069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133200381502653551366101379 199800572253980327049152069)
            ·
              refine ⟨37462607297621311321716013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199800572253980327049152069 37462607297621311321716013)
              ·
                refine ⟨14048477736607991745643505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37462607297621311321716013 14048477736607991745643505)
                ·
                  refine ⟨10536358302455993809232629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14048477736607991745643505 10536358302455993809232629)
                  ·
                    refine ⟨987783590855249419615559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10536358302455993809232629 987783590855249419615559)
                    ·
                      rfl

theorem cell23_5771105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_5771105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771105 prefixEnd_5771105 := by exact prefixLift 5771105
  have htrace : WordTrace (prefixWord ++ tailWord_5771105) baseStart_5771105 baseEnd_5771105 := by
    simpa [prefixWord, tailWord_5771105, baseEnd_5771105] using wordTrace_append hprefix tailTrace_5771105
  have hstable : (prefixWord ++ tailWord_5771105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771105).length < 2 ^ (prefixWord ++ tailWord_5771105).sum := by decide
  have hdescent : baseEnd_5771105 < baseStart_5771105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771126 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_5771126 : Nat := 118140960795 + 5771126 * 2 ^ 59
def prefixEnd_5771126 : Nat := 4983230072969 + 3 ^ 40 * 5771126 * 2
def baseEnd_5771126 : Nat := 329262395073276964076009

theorem tailTrace_5771126 : CollatzResearch.WordTrace tailWord_5771126 prefixEnd_5771126 329262395073276964076009 := by
  unfold tailWord_5771126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13155641105637725418494327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140326838460135737797272821 13155641105637725418494327)
  ·
    refine ⟨19733461658456588127741491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13155641105637725418494327 19733461658456588127741491)
    ·
      refine ⟨29600192487684882191612237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19733461658456588127741491 29600192487684882191612237)
      ·
        refine ⟨11100072182881830821854589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29600192487684882191612237 11100072182881830821854589)
        ·
          refine ⟨4162527068580686558195471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11100072182881830821854589 4162527068580686558195471)
          ·
            refine ⟨6243790602871029837293207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162527068580686558195471 6243790602871029837293207)
            ·
              refine ⟨9365685904306544755939811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243790602871029837293207 9365685904306544755939811)
              ·
                refine ⟨14048528856459817133909717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9365685904306544755939811 14048528856459817133909717)
                ·
                  refine ⟨329262395073276964076009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14048528856459817133909717 329262395073276964076009)
                  ·
                    rfl

theorem cell23_5771126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_5771126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771126 prefixEnd_5771126 := by exact prefixLift 5771126
  have htrace : WordTrace (prefixWord ++ tailWord_5771126) baseStart_5771126 baseEnd_5771126 := by
    simpa [prefixWord, tailWord_5771126, baseEnd_5771126] using wordTrace_append hprefix tailTrace_5771126
  have hstable : (prefixWord ++ tailWord_5771126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771126).length < 2 ^ (prefixWord ++ tailWord_5771126).sum := by decide
  have hdescent : baseEnd_5771126 < baseStart_5771126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771137 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5771137 : Nat := 118140960795 + 5771137 * 2 ^ 59
def prefixEnd_5771137 : Nat := 4983230072969 + 3 ^ 40 * 5771137 * 2
def baseEnd_5771137 : Nat := 2963367203946692133646531

theorem tailTrace_5771137 : CollatzResearch.WordTrace tailWord_5771137 prefixEnd_5771137 2963367203946692133646531 := by
  unfold tailWord_5771137
  simp only [CollatzResearch.WordTrace]
  refine ⟨210490658893163755574559665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140327105928775837049706443 210490658893163755574559665)
  ·
    refine ⟨157867994169872816680919749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210490658893163755574559665 157867994169872816680919749)
    ·
      refine ⟨29600248906851153127672453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157867994169872816680919749 29600248906851153127672453)
      ·
        refine ⟨5550046670034591211438585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29600248906851153127672453 5550046670034591211438585)
        ·
          refine ⟨4162535002525943408578939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5550046670034591211438585 4162535002525943408578939)
          ·
            refine ⟨6243802503788915112868409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162535002525943408578939 6243802503788915112868409)
            ·
              refine ⟨4682851877841686334651307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6243802503788915112868409 4682851877841686334651307)
              ·
                refine ⟨7024277816762529501976961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4682851877841686334651307 7024277816762529501976961)
                ·
                  refine ⟨5268208362571897126482721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7024277816762529501976961 5268208362571897126482721)
                  ·
                    refine ⟨3951156271928922844862041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5268208362571897126482721 3951156271928922844862041)
                    ·
                      refine ⟨2963367203946692133646531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951156271928922844862041 2963367203946692133646531)
                      ·
                        rfl

theorem cell23_5771137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5771137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771137 prefixEnd_5771137 := by exact prefixLift 5771137
  have htrace : WordTrace (prefixWord ++ tailWord_5771137) baseStart_5771137 baseEnd_5771137 := by
    simpa [prefixWord, tailWord_5771137, baseEnd_5771137] using wordTrace_append hprefix tailTrace_5771137
  have hstable : (prefixWord ++ tailWord_5771137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771137).length < 2 ^ (prefixWord ++ tailWord_5771137).sum := by decide
  have hdescent : baseEnd_5771137 < baseStart_5771137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771195 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 3, 5]
def baseStart_5771195 : Nat := 118140960795 + 5771195 * 2 ^ 59
def prefixEnd_5771195 : Nat := 4983230072969 + 3 ^ 40 * 5771195 * 2
def baseEnd_5771195 : Nat := 987798995274884302240421

theorem tailTrace_5771195 : CollatzResearch.WordTrace tailWord_5771195 prefixEnd_5771195 987798995274884302240421 := by
  unfold tailWord_5771195
  simp only [CollatzResearch.WordTrace]
  refine ⟨210492774326953631480171039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140328516217969087653447359 210492774326953631480171039)
  ·
    refine ⟨315739161490430447220256559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210492774326953631480171039 315739161490430447220256559)
    ·
      refine ⟨473608742235645670830384839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315739161490430447220256559 473608742235645670830384839)
      ·
        refine ⟨710413113353468506245577259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473608742235645670830384839 710413113353468506245577259)
        ·
          refine ⟨1065619670030202759368365889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710413113353468506245577259 1065619670030202759368365889)
          ·
            refine ⟨799214752522652069526274417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065619670030202759368365889 799214752522652069526274417)
            ·
              refine ⟨599411064391989052144705813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799214752522652069526274417 599411064391989052144705813)
              ·
                refine ⟨28097393643374486819283085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 599411064391989052144705813 28097393643374486819283085)
                ·
                  refine ⟨10536522616265432557231157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28097393643374486819283085 10536522616265432557231157)
                  ·
                    refine ⟨987798995274884302240421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10536522616265432557231157 987798995274884302240421)
                    ·
                      rfl

theorem cell23_5771195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 5].length) (baseStart_5771195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771195 prefixEnd_5771195 := by exact prefixLift 5771195
  have htrace : WordTrace (prefixWord ++ tailWord_5771195) baseStart_5771195 baseEnd_5771195 := by
    simpa [prefixWord, tailWord_5771195, baseEnd_5771195] using wordTrace_append hprefix tailTrace_5771195
  have hstable : (prefixWord ++ tailWord_5771195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771195).length < 2 ^ (prefixWord ++ tailWord_5771195).sum := by decide
  have hdescent : baseEnd_5771195 < baseStart_5771195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771212 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_5771212 : Nat := 118140960795 + 5771212 * 2 ^ 59
def prefixEnd_5771212 : Nat := 4983230072969 + 3 ^ 40 * 5771212 * 2
def baseEnd_5771212 : Nat := 987801904998593113402895

theorem tailTrace_5771212 : CollatzResearch.WordTrace tailWord_5771212 prefixEnd_5771212 987801904998593113402895 := by
  unfold tailWord_5771212
  simp only [CollatzResearch.WordTrace]
  refine ⟨105246697183946021691769945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140328929578594695589026593 105246697183946021691769945)
  ·
    refine ⟨78935022887959516268827459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105246697183946021691769945 78935022887959516268827459)
    ·
      refine ⟨118402534331939274403241189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78935022887959516268827459 118402534331939274403241189)
      ·
        refine ⟨22200475187238613950607723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118402534331939274403241189 22200475187238613950607723)
        ·
          refine ⟨33300712780857920925911585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22200475187238613950607723 33300712780857920925911585)
          ·
            refine ⟨24975534585643440694433689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33300712780857920925911585 24975534585643440694433689)
            ·
              refine ⟨18731650939232580520825267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24975534585643440694433689 18731650939232580520825267)
              ·
                refine ⟨28097476408848870781237901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18731650939232580520825267 28097476408848870781237901)
                ·
                  refine ⟨10536553653318326542964213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28097476408848870781237901 10536553653318326542964213)
                  ·
                    refine ⟨987801904998593113402895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10536553653318326542964213 987801904998593113402895)
                    ·
                      rfl

theorem cell23_5771212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_5771212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771212 prefixEnd_5771212 := by exact prefixLift 5771212
  have htrace : WordTrace (prefixWord ++ tailWord_5771212) baseStart_5771212 baseEnd_5771212 := by
    simpa [prefixWord, tailWord_5771212, baseEnd_5771212] using wordTrace_append hprefix tailTrace_5771212
  have hstable : (prefixWord ++ tailWord_5771212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771212).length < 2 ^ (prefixWord ++ tailWord_5771212).sum := by decide
  have hdescent : baseEnd_5771212 < baseStart_5771212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771232 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 8, 2]
def baseStart_5771232 : Nat := 118140960795 + 5771232 * 2 ^ 59
def prefixEnd_5771232 : Nat := 4983230072969 + 3 ^ 40 * 5771232 * 2
def baseEnd_5771232 : Nat := 2963415984608869261958593

theorem tailTrace_5771232 : CollatzResearch.WordTrace tailWord_5771232 prefixEnd_5771232 2963415984608869261958593 := by
  unfold tailWord_5771232
  simp only [CollatzResearch.WordTrace]
  refine ⟨105247061913909793399633975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140329415885213057866178633 105247061913909793399633975)
  ·
    refine ⟨157870592870864690099450963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105247061913909793399633975 157870592870864690099450963)
    ·
      refine ⟨236805889306297035149176445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157870592870864690099450963 236805889306297035149176445)
      ·
        refine ⟨88802208489861388180941167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236805889306297035149176445 88802208489861388180941167)
        ·
          refine ⟨133203312734792082271411751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88802208489861388180941167 133203312734792082271411751)
          ·
            refine ⟨199804969102188123407117627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133203312734792082271411751 199804969102188123407117627)
            ·
              refine ⟨299707453653282185110676441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199804969102188123407117627 299707453653282185110676441)
              ·
                refine ⟨224780590239961638833007331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299707453653282185110676441 224780590239961638833007331)
                ·
                  refine ⟨337170885359942458249510997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224780590239961638833007331 337170885359942458249510997)
                  ·
                    refine ⟨3951221312811825682611457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 337170885359942458249510997 3951221312811825682611457)
                    ·
                      refine ⟨2963415984608869261958593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951221312811825682611457 2963415984608869261958593)
                      ·
                        rfl

theorem cell23_5771232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_5771232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771232 prefixEnd_5771232 := by exact prefixLift 5771232
  have htrace : WordTrace (prefixWord ++ tailWord_5771232) baseStart_5771232 baseEnd_5771232 := by
    simpa [prefixWord, tailWord_5771232, baseEnd_5771232] using wordTrace_append hprefix tailTrace_5771232
  have hstable : (prefixWord ++ tailWord_5771232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771232).length < 2 ^ (prefixWord ++ tailWord_5771232).sum := by decide
  have hdescent : baseEnd_5771232 < baseStart_5771232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771269 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_5771269 : Nat := 118140960795 + 5771269 * 2 ^ 59
def prefixEnd_5771269 : Nat := 4983230072969 + 3 ^ 40 * 5771269 * 2
def baseEnd_5771269 : Nat := 2963434983393085617195923

theorem tailTrace_5771269 : CollatzResearch.WordTrace tailWord_5771269 prefixEnd_5771269 2963434983393085617195923 := by
  unfold tailWord_5771269
  simp only [CollatzResearch.WordTrace]
  refine ⟨210495473328685542118364861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140330315552457028078909907 210495473328685542118364861)
  ·
    refine ⟨78935802498257078294386823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210495473328685542118364861 78935802498257078294386823)
    ·
      refine ⟨118403703747385617441580235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78935802498257078294386823 118403703747385617441580235)
      ·
        refine ⟨177605555621078426162370353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118403703747385617441580235 177605555621078426162370353)
        ·
          refine ⟨133204166715808819621777765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177605555621078426162370353 133204166715808819621777765)
          ·
            refine ⟨24975781259214153679083331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133204166715808819621777765 24975781259214153679083331)
            ·
              refine ⟨37463671888821230518624997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24975781259214153679083331 37463671888821230518624997)
              ·
                refine ⟨7024438479153980722242187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37463671888821230518624997 7024438479153980722242187)
                ·
                  refine ⟨10536657718730971083363281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7024438479153980722242187 10536657718730971083363281)
                  ·
                    refine ⟨7902493289048228312522461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10536657718730971083363281 7902493289048228312522461)
                    ·
                      refine ⟨2963434983393085617195923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7902493289048228312522461 2963434983393085617195923)
                      ·
                        rfl

theorem cell23_5771269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_5771269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771269 prefixEnd_5771269 := by exact prefixLift 5771269
  have htrace : WordTrace (prefixWord ++ tailWord_5771269) baseStart_5771269 baseEnd_5771269 := by
    simpa [prefixWord, tailWord_5771269, baseEnd_5771269] using wordTrace_append hprefix tailTrace_5771269
  have hstable : (prefixWord ++ tailWord_5771269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771269).length < 2 ^ (prefixWord ++ tailWord_5771269).sum := by decide
  have hdescent : baseEnd_5771269 < baseStart_5771269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771283 : List Nat := [1, 1, 1, 2, 1, 4, 5, 3, 1, 2, 2]
def baseStart_5771283 : Nat := 118140960795 + 5771283 * 2 ^ 59
def prefixEnd_5771283 : Nat := 4983230072969 + 3 ^ 40 * 5771283 * 2
def baseEnd_5771283 : Nat := 2963442172122248562420859

theorem tailTrace_5771283 : CollatzResearch.WordTrace tailWord_5771283 prefixEnd_5771283 2963442172122248562420859 := by
  unfold tailWord_5771283
  simp only [CollatzResearch.WordTrace]
  refine ⟨210495983950634822509374503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140330655967089881672916335 210495983950634822509374503)
  ·
    refine ⟨315743975925952233764061755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210495983950634822509374503 315743975925952233764061755)
    ·
      refine ⟨473615963888928350646092633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315743975925952233764061755 473615963888928350646092633)
      ·
        refine ⟨355211972916696262984569475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473615963888928350646092633 355211972916696262984569475)
        ·
          refine ⟨532817959375044394476854213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355211972916696262984569475 532817959375044394476854213)
          ·
            refine ⟨99903367382820823964410165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 532817959375044394476854213 99903367382820823964410165)
            ·
              refine ⟨9365940692139452246663453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99903367382820823964410165 9365940692139452246663453)
              ·
                refine ⟨3512227759552294592498795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9365940692139452246663453 3512227759552294592498795)
                ·
                  refine ⟨5268341639328441888748193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512227759552294592498795 5268341639328441888748193)
                  ·
                    refine ⟨3951256229496331416561145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5268341639328441888748193 3951256229496331416561145)
                    ·
                      refine ⟨2963442172122248562420859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951256229496331416561145 2963442172122248562420859)
                      ·
                        rfl

theorem cell23_5771283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 2, 2].length) (baseStart_5771283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771283 prefixEnd_5771283 := by exact prefixLift 5771283
  have htrace : WordTrace (prefixWord ++ tailWord_5771283) baseStart_5771283 baseEnd_5771283 := by
    simpa [prefixWord, tailWord_5771283, baseEnd_5771283] using wordTrace_append hprefix tailTrace_5771283
  have hstable : (prefixWord ++ tailWord_5771283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771283).length < 2 ^ (prefixWord ++ tailWord_5771283).sum := by decide
  have hdescent : baseEnd_5771283 < baseStart_5771283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771299 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 3]
def baseStart_5771299 : Nat := 118140960795 + 5771299 * 2 ^ 59
def prefixEnd_5771299 : Nat := 4983230072969 + 3 ^ 40 * 5771299 * 2
def baseEnd_5771299 : Nat := 2963450387812720499820785

theorem tailTrace_5771299 : CollatzResearch.WordTrace tailWord_5771299 prefixEnd_5771299 2963450387812720499820785 := by
  unfold tailWord_5771299
  simp only [CollatzResearch.WordTrace]
  refine ⟨210496567518576857241956951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140331045012384571494637967 210496567518576857241956951)
  ·
    refine ⟨315744851277865285862935427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210496567518576857241956951 315744851277865285862935427)
    ·
      refine ⟨473617276916797928794403141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315744851277865285862935427 473617276916797928794403141)
      ·
        refine ⟨88803239421899611648950589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 473617276916797928794403141 88803239421899611648950589)
        ·
          refine ⟨33301214783212354368356471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88803239421899611648950589 33301214783212354368356471)
          ·
            refine ⟨49951822174818531552534707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33301214783212354368356471 49951822174818531552534707)
            ·
              refine ⟨74927733262227797328802061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49951822174818531552534707 74927733262227797328802061)
              ·
                refine ⟨28097899973335423998300773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74927733262227797328802061 28097899973335423998300773)
                ·
                  refine ⟨5268356245000391999681395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28097899973335423998300773 5268356245000391999681395)
                  ·
                    refine ⟨7902534367500587999522093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5268356245000391999681395 7902534367500587999522093)
                    ·
                      refine ⟨2963450387812720499820785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7902534367500587999522093 2963450387812720499820785)
                      ·
                        rfl

theorem cell23_5771299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_5771299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771299 prefixEnd_5771299 := by exact prefixLift 5771299
  have htrace : WordTrace (prefixWord ++ tailWord_5771299) baseStart_5771299 baseEnd_5771299 := by
    simpa [prefixWord, tailWord_5771299, baseEnd_5771299] using wordTrace_append hprefix tailTrace_5771299
  have hstable : (prefixWord ++ tailWord_5771299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771299).length < 2 ^ (prefixWord ++ tailWord_5771299).sum := by decide
  have hdescent : baseEnd_5771299 < baseStart_5771299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771300 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_5771300 : Nat := 118140960795 + 5771300 * 2 ^ 59
def prefixEnd_5771300 : Nat := 4983230072969 + 3 ^ 40 * 5771300 * 2
def baseEnd_5771300 : Nat := 2963450901293374995908281

theorem tailTrace_5771300 : CollatzResearch.WordTrace tailWord_5771300 prefixEnd_5771300 2963450901293374995908281 := by
  unfold tailWord_5771300
  simp only [CollatzResearch.WordTrace]
  refine ⟨105248301995786617206371677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140331069327715489608495569 105248301995786617206371677)
  ·
    refine ⟨39468113248419981452389379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105248301995786617206371677 39468113248419981452389379)
    ·
      refine ⟨59202169872629972178584069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39468113248419981452389379 59202169872629972178584069)
      ·
        refine ⟨11100406851118119783484513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59202169872629972178584069 11100406851118119783484513)
        ·
          refine ⟨8325305138338589837613385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11100406851118119783484513 8325305138338589837613385)
          ·
            refine ⟨6243978853753942378210039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8325305138338589837613385 6243978853753942378210039)
            ·
              refine ⟨9365968280630913567315059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243978853753942378210039 9365968280630913567315059)
              ·
                refine ⟨14048952420946370350972589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9365968280630913567315059 14048952420946370350972589)
                ·
                  refine ⟨5268357157854888881614721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14048952420946370350972589 5268357157854888881614721)
                  ·
                    refine ⟨3951267868391166661211041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5268357157854888881614721 3951267868391166661211041)
                    ·
                      refine ⟨2963450901293374995908281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951267868391166661211041 2963450901293374995908281)
                      ·
                        rfl

theorem cell23_5771300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_5771300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771300 prefixEnd_5771300 := by exact prefixLift 5771300
  have htrace : WordTrace (prefixWord ++ tailWord_5771300) baseStart_5771300 baseEnd_5771300 := by
    simpa [prefixWord, tailWord_5771300, baseEnd_5771300] using wordTrace_append hprefix tailTrace_5771300
  have hstable : (prefixWord ++ tailWord_5771300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771300).length < 2 ^ (prefixWord ++ tailWord_5771300).sum := by decide
  have hdescent : baseEnd_5771300 < baseStart_5771300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771305 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_5771305 : Nat := 118140960795 + 5771305 * 2 ^ 59
def prefixEnd_5771305 : Nat := 4983230072969 + 3 ^ 40 * 5771305 * 2
def baseEnd_5771305 : Nat := 2963453468696647476345757

theorem tailTrace_5771305 : CollatzResearch.WordTrace tailWord_5771305 prefixEnd_5771305 2963453468696647476345757 := by
  unfold tailWord_5771305
  simp only [CollatzResearch.WordTrace]
  refine ⟨210496786356555120266675369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140331190904370080177783579 210496786356555120266675369)
  ·
    refine ⟨157872589767416340200006527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210496786356555120266675369 157872589767416340200006527)
    ·
      refine ⟨236808884651124510300009791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157872589767416340200006527 236808884651124510300009791)
      ·
        refine ⟨355213326976686765450014687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236808884651124510300009791 355213326976686765450014687)
        ·
          refine ⟨532819990465030148175022031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355213326976686765450014687 532819990465030148175022031)
          ·
            refine ⟨799229985697545222262533047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532819990465030148175022031 799229985697545222262533047)
            ·
              refine ⟨1198844978546317833393799571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799229985697545222262533047 1198844978546317833393799571)
              ·
                refine ⟨1798267467819476750090699357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198844978546317833393799571 1798267467819476750090699357)
                ·
                  refine ⟨674350300432303781284012259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1798267467819476750090699357 674350300432303781284012259)
                  ·
                    refine ⟨1011525450648455671926018389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 674350300432303781284012259 1011525450648455671926018389)
                    ·
                      refine ⟨2963453468696647476345757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1011525450648455671926018389 2963453468696647476345757)
                      ·
                        rfl

theorem cell23_5771305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_5771305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771305 prefixEnd_5771305 := by exact prefixLift 5771305
  have htrace : WordTrace (prefixWord ++ tailWord_5771305) baseStart_5771305 baseEnd_5771305 := by
    simpa [prefixWord, tailWord_5771305, baseEnd_5771305] using wordTrace_append hprefix tailTrace_5771305
  have hstable : (prefixWord ++ tailWord_5771305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771305).length < 2 ^ (prefixWord ++ tailWord_5771305).sum := by decide
  have hdescent : baseEnd_5771305 < baseStart_5771305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771339 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 1, 4, 2]
def baseStart_5771339 : Nat := 118140960795 + 5771339 * 2 ^ 59
def prefixEnd_5771339 : Nat := 4983230072969 + 3 ^ 40 * 5771339 * 2
def baseEnd_5771339 : Nat := 2963470927038900343320601

theorem tailTrace_5771339 : CollatzResearch.WordTrace tailWord_5771339 prefixEnd_5771339 2963470927038900343320601 := by
  unfold tailWord_5771339
  simp only [CollatzResearch.WordTrace]
  refine ⟨210498026438431944073413071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140332017625621296048942047 210498026438431944073413071)
  ·
    refine ⟨315747039657647916110119607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210498026438431944073413071 315747039657647916110119607)
    ·
      refine ⟨473620559486471874165179411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315747039657647916110119607 473620559486471874165179411)
      ·
        refine ⟨710430839229707811247769117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473620559486471874165179411 710430839229707811247769117)
        ·
          refine ⟨266411564711140429217913419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 710430839229707811247769117 266411564711140429217913419)
          ·
            refine ⟨399617347066710643826870129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266411564711140429217913419 399617347066710643826870129)
            ·
              refine ⟨299713010300032982870152597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399617347066710643826870129 299713010300032982870152597)
              ·
                refine ⟨14049047357814046072038403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 299713010300032982870152597 14049047357814046072038403)
                ·
                  refine ⟨21073571036721069108057605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14049047357814046072038403 21073571036721069108057605)
                  ·
                    refine ⟨3951294569385200457760801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21073571036721069108057605 3951294569385200457760801)
                    ·
                      refine ⟨2963470927038900343320601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951294569385200457760801 2963470927038900343320601)
                      ·
                        rfl

theorem cell23_5771339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 4, 2].length) (baseStart_5771339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771339 prefixEnd_5771339 := by exact prefixLift 5771339
  have htrace : WordTrace (prefixWord ++ tailWord_5771339) baseStart_5771339 baseEnd_5771339 := by
    simpa [prefixWord, tailWord_5771339, baseEnd_5771339] using wordTrace_append hprefix tailTrace_5771339
  have hstable : (prefixWord ++ tailWord_5771339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771339).length < 2 ^ (prefixWord ++ tailWord_5771339).sum := by decide
  have hdescent : baseEnd_5771339 < baseStart_5771339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
