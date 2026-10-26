import V185TrunkScan23Chunk0231

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1371916 : List Nat := [2, 2, 1, 2, 2, 1, 6, 7]
def baseStart_1371916 : Nat := 118140960795 + 1371916 * 2 ^ 59
def prefixEnd_1371916 : Nat := 4983230072969 + 3 ^ 40 * 1371916 * 2
def baseEnd_1371916 : Nat := 26090826873842948371877

theorem tailTrace_1371916 : CollatzResearch.WordTrace tailWord_1371916 prefixEnd_1371916 26090826873842948371877 := by
  unfold tailWord_1371916
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018943648895055721983801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33358591531860074295978401 25018943648895055721983801)
  ·
    refine ⟨18764207736671291791487851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25018943648895055721983801 18764207736671291791487851)
    ·
      refine ⟨28146311605006937687231777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18764207736671291791487851 28146311605006937687231777)
      ·
        refine ⟨21109733703755203265423833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28146311605006937687231777 21109733703755203265423833)
        ·
          refine ⟨15832300277816402449067875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21109733703755203265423833 15832300277816402449067875)
          ·
            refine ⟨23748450416724603673601813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15832300277816402449067875 23748450416724603673601813)
            ·
              refine ⟨1113208613283965797200085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23748450416724603673601813 1113208613283965797200085)
              ·
                refine ⟨26090826873842948371877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1113208613283965797200085 26090826873842948371877)
                ·
                  rfl

theorem cell23_1371916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 7].length) (baseStart_1371916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371916 prefixEnd_1371916 := by exact prefixLift 1371916
  have htrace : WordTrace (prefixWord ++ tailWord_1371916) baseStart_1371916 baseEnd_1371916 := by
    simpa [prefixWord, tailWord_1371916, baseEnd_1371916] using wordTrace_append hprefix tailTrace_1371916
  have hstable : (prefixWord ++ tailWord_1371916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371916).length < 2 ^ (prefixWord ++ tailWord_1371916).sum := by decide
  have hdescent : baseEnd_1371916 < baseStart_1371916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371960 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_1371960 : Nat := 118140960795 + 1371960 * 2 ^ 59
def prefixEnd_1371960 : Nat := 4983230072969 + 3 ^ 40 * 1371960 * 2
def baseEnd_1371960 : Nat := 704474918742557433890477

theorem tailTrace_1371960 : CollatzResearch.WordTrace tailWord_1371960 prefixEnd_1371960 704474918742557433890477 := by
  unfold tailWord_1371960
  simp only [CollatzResearch.WordTrace]
  refine ⟨25019746054815353479284667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33359661406420471305712889 25019746054815353479284667)
  ·
    refine ⟨37529619082223030218927001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25019746054815353479284667 37529619082223030218927001)
    ·
      refine ⟨28147214311667272664195251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37529619082223030218927001 28147214311667272664195251)
      ·
        refine ⟨42220821467500908996292877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28147214311667272664195251 42220821467500908996292877)
        ·
          refine ⟨15832808050312840873609829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42220821467500908996292877 15832808050312840873609829)
          ·
            refine ⟨2968651509433657663801843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15832808050312840873609829 2968651509433657663801843)
            ·
              refine ⟨4452977264150486495702765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968651509433657663801843 4452977264150486495702765)
              ·
                refine ⟨1669866474056432435888537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4452977264150486495702765 1669866474056432435888537)
                ·
                  refine ⟨1252399855542324326916403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1669866474056432435888537 1252399855542324326916403)
                  ·
                    refine ⟨1878599783313486490374605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252399855542324326916403 1878599783313486490374605)
                    ·
                      refine ⟨704474918742557433890477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878599783313486490374605 704474918742557433890477)
                      ·
                        rfl

theorem cell23_1371960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_1371960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371960 prefixEnd_1371960 := by exact prefixLift 1371960
  have htrace : WordTrace (prefixWord ++ tailWord_1371960) baseStart_1371960 baseEnd_1371960 := by
    simpa [prefixWord, tailWord_1371960, baseEnd_1371960] using wordTrace_append hprefix tailTrace_1371960
  have hstable : (prefixWord ++ tailWord_1371960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371960).length < 2 ^ (prefixWord ++ tailWord_1371960).sum := by decide
  have hdescent : baseEnd_1371960 < baseStart_1371960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372010 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1372010 : Nat := 118140960795 + 1372010 * 2 ^ 59
def prefixEnd_1372010 : Nat := 4983230072969 + 3 ^ 40 * 1372010 * 2
def baseEnd_1372010 : Nat := 234833530925094079421749

theorem tailTrace_1372010 : CollatzResearch.WordTrace tailWord_1372010 prefixEnd_1372010 234833530925094079421749 := by
  unfold tailWord_1372010
  simp only [CollatzResearch.WordTrace]
  refine ⟨12510328939862391374472371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33360877172966376998592989 12510328939862391374472371)
  ·
    refine ⟨18765493409793587061708557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12510328939862391374472371 18765493409793587061708557)
    ·
      refine ⟨7037060028672595148140709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18765493409793587061708557 7037060028672595148140709)
      ·
        refine ⟨1319448755376111590276383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7037060028672595148140709 1319448755376111590276383)
        ·
          refine ⟨1979173133064167385414575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319448755376111590276383 1979173133064167385414575)
          ·
            refine ⟨2968759699596251078121863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979173133064167385414575 2968759699596251078121863)
            ·
              refine ⟨4453139549394376617182795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968759699596251078121863 4453139549394376617182795)
              ·
                refine ⟨6679709324091564925774193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453139549394376617182795 6679709324091564925774193)
                ·
                  refine ⟨5009781993068673694330645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6679709324091564925774193 5009781993068673694330645)
                  ·
                    refine ⟨234833530925094079421749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5009781993068673694330645 234833530925094079421749)
                    ·
                      rfl

theorem cell23_1372010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1372010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372010 prefixEnd_1372010 := by exact prefixLift 1372010
  have htrace : WordTrace (prefixWord ++ tailWord_1372010) baseStart_1372010 baseEnd_1372010 := by
    simpa [prefixWord, tailWord_1372010, baseEnd_1372010] using wordTrace_append hprefix tailTrace_1372010
  have hstable : (prefixWord ++ tailWord_1372010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372010).length < 2 ^ (prefixWord ++ tailWord_1372010).sum := by decide
  have hdescent : baseEnd_1372010 < baseStart_1372010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372050 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1372050 : Nat := 118140960795 + 1372050 * 2 ^ 59
def prefixEnd_1372050 : Nat := 4983230072969 + 3 ^ 40 * 1372050 * 2
def baseEnd_1372050 : Nat := 704521132001462081765063

theorem tailTrace_1372050 : CollatzResearch.WordTrace tailWord_1372050 prefixEnd_1372050 704521132001462081765063 := by
  unfold tailWord_1372050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12510693669826163082336401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33361849786203101552897069 12510693669826163082336401)
  ·
    refine ⟨9383020252369622311752301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12510693669826163082336401 9383020252369622311752301)
    ·
      refine ⟨3518632594638608366907113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9383020252369622311752301 3518632594638608366907113)
      ·
        refine ⟨2638974445978956275180335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3518632594638608366907113 2638974445978956275180335)
        ·
          refine ⟨3958461668968434412770503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2638974445978956275180335 3958461668968434412770503)
          ·
            refine ⟨5937692503452651619155755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958461668968434412770503 5937692503452651619155755)
            ·
              refine ⟨8906538755178977428733633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937692503452651619155755 8906538755178977428733633)
              ·
                refine ⟨6679904066384233071550225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8906538755178977428733633 6679904066384233071550225)
                ·
                  refine ⟨5009928049788174803662669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6679904066384233071550225 5009928049788174803662669)
                  ·
                    refine ⟨1878723018670565551373501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5009928049788174803662669 1878723018670565551373501)
                    ·
                      refine ⟨704521132001462081765063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878723018670565551373501 704521132001462081765063)
                      ·
                        rfl

theorem cell23_1372050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1372050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372050 prefixEnd_1372050 := by exact prefixLift 1372050
  have htrace : WordTrace (prefixWord ++ tailWord_1372050) baseStart_1372050 baseEnd_1372050 := by
    simpa [prefixWord, tailWord_1372050, baseEnd_1372050] using wordTrace_append hprefix tailTrace_1372050
  have hstable : (prefixWord ++ tailWord_1372050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372050).length < 2 ^ (prefixWord ++ tailWord_1372050).sum := by decide
  have hdescent : baseEnd_1372050 < baseStart_1372050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372073 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 1, 6, 2]
def baseStart_1372073 : Nat := 118140960795 + 1372073 * 2 ^ 59
def prefixEnd_1372073 : Nat := 4983230072969 + 3 ^ 40 * 1372073 * 2
def baseEnd_1372073 : Nat := 704532942056515491777457

theorem tailTrace_1372073 : CollatzResearch.WordTrace tailWord_1372073 prefixEnd_1372073 704532942056515491777457 := by
  unfold tailWord_1372073
  simp only [CollatzResearch.WordTrace]
  refine ⟨50043613558221327257432873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33362409038814218171621915 50043613558221327257432873)
  ·
    refine ⟨37532710168665995443074655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50043613558221327257432873 37532710168665995443074655)
    ·
      refine ⟨56299065252998993164611983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37532710168665995443074655 56299065252998993164611983)
      ·
        refine ⟨84448597879498489746917975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56299065252998993164611983 84448597879498489746917975)
        ·
          refine ⟨126672896819247734620376963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84448597879498489746917975 126672896819247734620376963)
          ·
            refine ⟨190009345228871601930565445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126672896819247734620376963 190009345228871601930565445)
            ·
              refine ⟨35626752230413425361981021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190009345228871601930565445 35626752230413425361981021)
              ·
                refine ⟨13360032086405034510742883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35626752230413425361981021 13360032086405034510742883)
                ·
                  refine ⟨20040048129607551766114325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13360032086405034510742883 20040048129607551766114325)
                  ·
                    refine ⟨939377256075353989036609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20040048129607551766114325 939377256075353989036609)
                    ·
                      refine ⟨704532942056515491777457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939377256075353989036609 704532942056515491777457)
                      ·
                        rfl

theorem cell23_1372073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 6, 2].length) (baseStart_1372073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372073 prefixEnd_1372073 := by exact prefixLift 1372073
  have htrace : WordTrace (prefixWord ++ tailWord_1372073) baseStart_1372073 baseEnd_1372073 := by
    simpa [prefixWord, tailWord_1372073, baseEnd_1372073] using wordTrace_append hprefix tailTrace_1372073
  have hstable : (prefixWord ++ tailWord_1372073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372073).length < 2 ^ (prefixWord ++ tailWord_1372073).sum := by decide
  have hdescent : baseEnd_1372073 < baseStart_1372073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372083 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 3, 4]
def baseStart_1372083 : Nat := 118140960795 + 1372083 * 2 ^ 59
def prefixEnd_1372083 : Nat := 4983230072969 + 3 ^ 40 * 1372083 * 2
def baseEnd_1372083 : Nat := 234846025621020150884137

theorem tailTrace_1372083 : CollatzResearch.WordTrace tailWord_1372083 prefixEnd_1372083 234846025621020150884137 := by
  unfold tailWord_1372083
  simp only [CollatzResearch.WordTrace]
  refine ⟨50043978288185098965296903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33362652192123399310197935 50043978288185098965296903)
  ·
    refine ⟨75065967432277648447945355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50043978288185098965296903 75065967432277648447945355)
    ·
      refine ⟨112598951148416472671918033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75065967432277648447945355 112598951148416472671918033)
      ·
        refine ⟨84449213361312354503938525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112598951148416472671918033 84449213361312354503938525)
        ·
          refine ⟨31668455010492132938976947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84449213361312354503938525 31668455010492132938976947)
          ·
            refine ⟨47502682515738199408465421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31668455010492132938976947 47502682515738199408465421)
            ·
              refine ⟨17813505943401824778174533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47502682515738199408465421 17813505943401824778174533)
              ·
                refine ⟨3340032364387842145907725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17813505943401824778174533 3340032364387842145907725)
                ·
                  refine ⟨1252512136645440804715397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3340032364387842145907725 1252512136645440804715397)
                  ·
                    refine ⟨234846025621020150884137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1252512136645440804715397 234846025621020150884137)
                    ·
                      rfl

theorem cell23_1372083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 4].length) (baseStart_1372083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372083 prefixEnd_1372083 := by exact prefixLift 1372083
  have htrace : WordTrace (prefixWord ++ tailWord_1372083) baseStart_1372083 baseEnd_1372083 := by
    simpa [prefixWord, tailWord_1372083, baseEnd_1372083] using wordTrace_append hprefix tailTrace_1372083
  have hstable : (prefixWord ++ tailWord_1372083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372083).length < 2 ^ (prefixWord ++ tailWord_1372083).sum := by decide
  have hdescent : baseEnd_1372083 < baseStart_1372083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372096 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 10]
def baseStart_1372096 : Nat := 118140960795 + 1372096 * 2 ^ 59
def prefixEnd_1372096 : Nat := 4983230072969 + 3 ^ 40 * 1372096 * 2
def baseEnd_1372096 : Nat := 78282750234618766865539

theorem tailTrace_1372096 : CollatzResearch.WordTrace tailWord_1372096 prefixEnd_1372096 78282750234618766865539 := by
  unfold tailWord_1372096
  simp only [CollatzResearch.WordTrace]
  refine ⟨25022226218569001092760071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33362968291425334790346761 25022226218569001092760071)
  ·
    refine ⟨37533339327853501639140107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25022226218569001092760071 37533339327853501639140107)
    ·
      refine ⟨56300008991780252458710161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37533339327853501639140107 56300008991780252458710161)
      ·
        refine ⟨42225006743835189344032621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56300008991780252458710161 42225006743835189344032621)
        ·
          refine ⟨15834377528938196004012233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42225006743835189344032621 15834377528938196004012233)
          ·
            refine ⟨11875783146703647003009175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15834377528938196004012233 11875783146703647003009175)
            ·
              refine ⟨17813674720055470504513763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11875783146703647003009175 17813674720055470504513763)
              ·
                refine ⟨26720512080083205756770645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17813674720055470504513763 26720512080083205756770645)
                ·
                  refine ⟨78282750234618766865539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 26720512080083205756770645 78282750234618766865539)
                  ·
                    rfl

theorem cell23_1372096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 10].length) (baseStart_1372096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372096 prefixEnd_1372096 := by exact prefixLift 1372096
  have htrace : WordTrace (prefixWord ++ tailWord_1372096) baseStart_1372096 baseEnd_1372096 := by
    simpa [prefixWord, tailWord_1372096, baseEnd_1372096] using wordTrace_append hprefix tailTrace_1372096
  have hstable : (prefixWord ++ tailWord_1372096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372096).length < 2 ^ (prefixWord ++ tailWord_1372096).sum := by decide
  have hdescent : baseEnd_1372096 < baseStart_1372096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372110 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_1372110 : Nat := 118140960795 + 1372110 * 2 ^ 59
def prefixEnd_1372110 : Nat := 4983230072969 + 3 ^ 40 * 1372110 * 2
def baseEnd_1372110 : Nat := 704551940840731847014787

theorem tailTrace_1372110 : CollatzResearch.WordTrace tailWord_1372110 prefixEnd_1372110 704551940840731847014787 := by
  unfold tailWord_1372110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6255620382385910322066223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33363308706058188384353189 6255620382385910322066223)
  ·
    refine ⟨9383430573578865483099335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6255620382385910322066223 9383430573578865483099335)
    ·
      refine ⟨14075145860368298224649003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9383430573578865483099335 14075145860368298224649003)
      ·
        refine ⟨21112718790552447336973505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14075145860368298224649003 21112718790552447336973505)
        ·
          refine ⟨15834539092914335502730129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21112718790552447336973505 15834539092914335502730129)
          ·
            refine ⟨11875904319685751627047597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15834539092914335502730129 11875904319685751627047597)
            ·
              refine ⟨4453464119882156860142849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11875904319685751627047597 4453464119882156860142849)
              ·
                refine ⟨3340098089911617645107137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4453464119882156860142849 3340098089911617645107137)
                ·
                  refine ⟨2505073567433713233830353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340098089911617645107137 2505073567433713233830353)
                  ·
                    refine ⟨1878805175575284925372765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2505073567433713233830353 1878805175575284925372765)
                    ·
                      refine ⟨704551940840731847014787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878805175575284925372765 704551940840731847014787)
                      ·
                        rfl

theorem cell23_1372110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_1372110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372110 prefixEnd_1372110 := by exact prefixLift 1372110
  have htrace : WordTrace (prefixWord ++ tailWord_1372110) baseStart_1372110 baseEnd_1372110 := by
    simpa [prefixWord, tailWord_1372110, baseEnd_1372110] using wordTrace_append hprefix tailTrace_1372110
  have hstable : (prefixWord ++ tailWord_1372110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372110).length < 2 ^ (prefixWord ++ tailWord_1372110).sum := by decide
  have hdescent : baseEnd_1372110 < baseStart_1372110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372117 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_1372117 : Nat := 118140960795 + 1372117 * 2 ^ 59
def prefixEnd_1372117 : Nat := 4983230072969 + 3 ^ 40 * 1372117 * 2
def baseEnd_1372117 : Nat := 234851845068437773209085

theorem tailTrace_1372117 : CollatzResearch.WordTrace tailWord_1372117 prefixEnd_1372117 234851845068437773209085 := by
  unfold tailWord_1372117
  simp only [CollatzResearch.WordTrace]
  refine ⟨50045218370061922772034605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33363478913374615181356403 50045218370061922772034605)
  ·
    refine ⟨18766956888773221039512977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50045218370061922772034605 18766956888773221039512977)
    ·
      refine ⟨14075217666579915779634733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18766956888773221039512977 14075217666579915779634733)
      ·
        refine ⟨5278206624967468417363025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14075217666579915779634733 5278206624967468417363025)
        ·
          refine ⟨3958654968725601313022269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5278206624967468417363025 3958654968725601313022269)
          ·
            refine ⟨1484495613272100492383351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3958654968725601313022269 1484495613272100492383351)
            ·
              refine ⟨2226743419908150738575027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484495613272100492383351 2226743419908150738575027)
              ·
                refine ⟨3340115129862226107862541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226743419908150738575027 3340115129862226107862541)
                ·
                  refine ⟨1252543173698334790448453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3340115129862226107862541 1252543173698334790448453)
                  ·
                    refine ⟨234851845068437773209085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1252543173698334790448453 234851845068437773209085)
                    ·
                      rfl

theorem cell23_1372117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_1372117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372117 prefixEnd_1372117 := by exact prefixLift 1372117
  have htrace : WordTrace (prefixWord ++ tailWord_1372117) baseStart_1372117 baseEnd_1372117 := by
    simpa [prefixWord, tailWord_1372117, baseEnd_1372117] using wordTrace_append hprefix tailTrace_1372117
  have hstable : (prefixWord ++ tailWord_1372117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372117).length < 2 ^ (prefixWord ++ tailWord_1372117).sum := by decide
  have hdescent : baseEnd_1372117 < baseStart_1372117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372140 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_1372140 : Nat := 118140960795 + 1372140 * 2 ^ 59
def prefixEnd_1372140 : Nat := 4983230072969 + 3 ^ 40 * 1372140 * 2
def baseEnd_1372140 : Nat := 704567345260366729639649

theorem tailTrace_1372140 : CollatzResearch.WordTrace tailWord_1372140 prefixEnd_1372140 704567345260366729639649 := by
  unfold tailWord_1372140
  simp only [CollatzResearch.WordTrace]
  refine ⟨25023028624489298850060937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33364038165985731800081249 25023028624489298850060937)
  ·
    refine ⟨18767271468366974137545703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25023028624489298850060937 18767271468366974137545703)
    ·
      refine ⟨28150907202550461206318555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18767271468366974137545703 28150907202550461206318555)
      ·
        refine ⟨42226360803825691809477833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28150907202550461206318555 42226360803825691809477833)
        ·
          refine ⟨31669770602869268857108375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42226360803825691809477833 31669770602869268857108375)
          ·
            refine ⟨47504655904303903285662563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31669770602869268857108375 47504655904303903285662563)
            ·
              refine ⟨71256983856455854928493845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47504655904303903285662563 71256983856455854928493845)
              ·
                refine ⟨3340171118271368199773149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71256983856455854928493845 3340171118271368199773149)
                ·
                  refine ⟨1252564169351763074914931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3340171118271368199773149 1252564169351763074914931)
                  ·
                    refine ⟨1878846254027644612372397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252564169351763074914931 1878846254027644612372397)
                    ·
                      refine ⟨704567345260366729639649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878846254027644612372397 704567345260366729639649)
                      ·
                        rfl

theorem cell23_1372140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_1372140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372140 prefixEnd_1372140 := by exact prefixLift 1372140
  have htrace : WordTrace (prefixWord ++ tailWord_1372140) baseStart_1372140 baseEnd_1372140 := by
    simpa [prefixWord, tailWord_1372140, baseEnd_1372140] using wordTrace_append hprefix tailTrace_1372140
  have hstable : (prefixWord ++ tailWord_1372140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372140).length < 2 ^ (prefixWord ++ tailWord_1372140).sum := by decide
  have hdescent : baseEnd_1372140 < baseStart_1372140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372143 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 3, 5]
def baseStart_1372143 : Nat := 118140960795 + 1372143 * 2 ^ 59
def prefixEnd_1372143 : Nat := 4983230072969 + 3 ^ 40 * 1372143 * 2
def baseEnd_1372143 : Nat := 234856295234110072634045

theorem tailTrace_1372143 : CollatzResearch.WordTrace tailWord_1372143 prefixEnd_1372143 234856295234110072634045 := by
  unfold tailWord_1372143
  simp only [CollatzResearch.WordTrace]
  refine ⟨50046166667967729212481083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33364111111978486141654055 50046166667967729212481083)
  ·
    refine ⟨75069250001951593818721625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50046166667967729212481083 75069250001951593818721625)
    ·
      refine ⟨56301937501463695364041219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75069250001951593818721625 56301937501463695364041219)
      ·
        refine ⟨84452906252195543046061829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56301937501463695364041219 84452906252195543046061829)
        ·
          refine ⟨15834919922286664321136593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84452906252195543046061829 15834919922286664321136593)
          ·
            refine ⟨11876189941714998240852445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15834919922286664321136593 11876189941714998240852445)
            ·
              refine ⟨4453571228143124340319667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11876189941714998240852445 4453571228143124340319667)
              ·
                refine ⟨6680356842214686510479501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453571228143124340319667 6680356842214686510479501)
                ·
                  refine ⟨2505133815830507441429813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6680356842214686510479501 2505133815830507441429813)
                  ·
                    refine ⟨234856295234110072634045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2505133815830507441429813 234856295234110072634045)
                    ·
                      rfl

theorem cell23_1372143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_1372143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372143 prefixEnd_1372143 := by exact prefixLift 1372143
  have htrace : WordTrace (prefixWord ++ tailWord_1372143) baseStart_1372143 baseEnd_1372143 := by
    simpa [prefixWord, tailWord_1372143, baseEnd_1372143] using wordTrace_append hprefix tailTrace_1372143
  have hstable : (prefixWord ++ tailWord_1372143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372143).length < 2 ^ (prefixWord ++ tailWord_1372143).sum := by decide
  have hdescent : baseEnd_1372143 < baseStart_1372143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372167 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_1372167 : Nat := 118140960795 + 1372167 * 2 ^ 59
def prefixEnd_1372167 : Nat := 4983230072969 + 3 ^ 40 * 1372167 * 2
def baseEnd_1372167 : Nat := 704581209238038124002025

theorem tailTrace_1372167 : CollatzResearch.WordTrace tailWord_1372167 prefixEnd_1372167 704581209238038124002025 := by
  unfold tailWord_1372167
  simp only [CollatzResearch.WordTrace]
  refine ⟨50047042019880781311354755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33364694679920520874236503 50047042019880781311354755)
  ·
    refine ⟨75070563029821171967032133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50047042019880781311354755 75070563029821171967032133)
    ·
      refine ⟨14075730568091469743818525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75070563029821171967032133 14075730568091469743818525)
      ·
        refine ⟨5278398963034301153931947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14075730568091469743818525 5278398963034301153931947)
        ·
          refine ⟨7917598444551451730897921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278398963034301153931947 7917598444551451730897921)
          ·
            refine ⟨5938198833413588798173441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7917598444551451730897921 5938198833413588798173441)
            ·
              refine ⟨4453649125060191598630081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938198833413588798173441 4453649125060191598630081)
              ·
                refine ⟨3340236843795143698972561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4453649125060191598630081 3340236843795143698972561)
                ·
                  refine ⟨2505177632846357774229421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340236843795143698972561 2505177632846357774229421)
                  ·
                    refine ⟨939441612317384165336033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505177632846357774229421 939441612317384165336033)
                    ·
                      refine ⟨704581209238038124002025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939441612317384165336033 704581209238038124002025)
                      ·
                        rfl

theorem cell23_1372167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_1372167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372167 prefixEnd_1372167 := by exact prefixLift 1372167
  have htrace : WordTrace (prefixWord ++ tailWord_1372167) baseStart_1372167 baseEnd_1372167 := by
    simpa [prefixWord, tailWord_1372167, baseEnd_1372167] using wordTrace_append hprefix tailTrace_1372167
  have hstable : (prefixWord ++ tailWord_1372167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372167).length < 2 ^ (prefixWord ++ tailWord_1372167).sum := by decide
  have hdescent : baseEnd_1372167 < baseStart_1372167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372174 : List Nat := [4, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_1372174 : Nat := 118140960795 + 1372174 * 2 ^ 59
def prefixEnd_1372174 : Nat := 4983230072969 + 3 ^ 40 * 1372174 * 2
def baseEnd_1372174 : Nat := 704584803602619596614493

theorem tailTrace_1372174 : CollatzResearch.WordTrace tailWord_1372174 prefixEnd_1372174 704584803602619596614493 := by
  unfold tailWord_1372174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6255912166356927688357447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33364864887236947671239717 6255912166356927688357447)
  ·
    refine ⟨9383868249535391532536171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6255912166356927688357447 9383868249535391532536171)
    ·
      refine ⟨14075802374303087298804257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9383868249535391532536171 14075802374303087298804257)
      ·
        refine ⟨10556851780727315474103193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14075802374303087298804257 10556851780727315474103193)
        ·
          refine ⟨7917638835545486605577395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10556851780727315474103193 7917638835545486605577395)
          ·
            refine ⟨11876458253318229908366093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917638835545486605577395 11876458253318229908366093)
            ·
              refine ⟨4453671844994336215637285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11876458253318229908366093 4453671844994336215637285)
              ·
                refine ⟨835063470936438040431991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4453671844994336215637285 835063470936438040431991)
                ·
                  refine ⟨1252595206404657060647987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835063470936438040431991 1252595206404657060647987)
                  ·
                    refine ⟨1878892809606985590971981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252595206404657060647987 1878892809606985590971981)
                    ·
                      refine ⟨704584803602619596614493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878892809606985590971981 704584803602619596614493)
                      ·
                        rfl

theorem cell23_1372174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_1372174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372174 prefixEnd_1372174 := by exact prefixLift 1372174
  have htrace : WordTrace (prefixWord ++ tailWord_1372174) baseStart_1372174 baseEnd_1372174 := by
    simpa [prefixWord, tailWord_1372174, baseEnd_1372174] using wordTrace_append hprefix tailTrace_1372174
  have hstable : (prefixWord ++ tailWord_1372174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372174).length < 2 ^ (prefixWord ++ tailWord_1372174).sum := by decide
  have hdescent : baseEnd_1372174 < baseStart_1372174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372197 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 5, 2, 2]
def baseStart_1372197 : Nat := 118140960795 + 1372197 * 2 ^ 59
def prefixEnd_1372197 : Nat := 4983230072969 + 3 ^ 40 * 1372197 * 2
def baseEnd_1372197 : Nat := 704596613657673006626887

theorem tailTrace_1372197 : CollatzResearch.WordTrace tailWord_1372197 prefixEnd_1372197 704596613657673006626887 := by
  unfold tailWord_1372197
  simp only [CollatzResearch.WordTrace]
  refine ⟨50048136209772096434946845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33365424139848064289964563 50048136209772096434946845)
  ·
    refine ⟨18768051078664536163105067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50048136209772096434946845 18768051078664536163105067)
    ·
      refine ⟨28152076617996804244657601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18768051078664536163105067 28152076617996804244657601)
      ·
        refine ⟨21114057463497603183493201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28152076617996804244657601 21114057463497603183493201)
        ·
          refine ⟨15835543097623202387619901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21114057463497603183493201 15835543097623202387619901)
          ·
            refine ⟨5938328661608700895357463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15835543097623202387619901 5938328661608700895357463)
            ·
              refine ⟨8907492992413051343036195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938328661608700895357463 8907492992413051343036195)
              ·
                refine ⟨13361239488619577014554293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8907492992413051343036195 13361239488619577014554293)
                ·
                  refine ⟨1252616202058085345114465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13361239488619577014554293 1252616202058085345114465)
                  ·
                    refine ⟨939462151543564008835849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1252616202058085345114465 939462151543564008835849)
                    ·
                      refine ⟨704596613657673006626887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939462151543564008835849 704596613657673006626887)
                      ·
                        rfl

theorem cell23_1372197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_1372197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372197 prefixEnd_1372197 := by exact prefixLift 1372197
  have htrace : WordTrace (prefixWord ++ tailWord_1372197) baseStart_1372197 baseEnd_1372197 := by
    simpa [prefixWord, tailWord_1372197, baseEnd_1372197] using wordTrace_append hprefix tailTrace_1372197
  have hstable : (prefixWord ++ tailWord_1372197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372197).length < 2 ^ (prefixWord ++ tailWord_1372197).sum := by decide
  have hdescent : baseEnd_1372197 < baseStart_1372197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372210 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1372210 : Nat := 118140960795 + 1372210 * 2 ^ 59
def prefixEnd_1372210 : Nat := 4983230072969 + 3 ^ 40 * 1372210 * 2
def baseEnd_1372210 : Nat := 704603288906181455764327

theorem tailTrace_1372210 : CollatzResearch.WordTrace tailWord_1372210 prefixEnd_1372210 704603288906181455764327 := by
  unfold tailWord_1372210
  simp only [CollatzResearch.WordTrace]
  refine ⟨12512152589681249913792521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33365740239149999770113389 12512152589681249913792521)
  ·
    refine ⟨9384114442260937435344391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12512152589681249913792521 9384114442260937435344391)
    ·
      refine ⟨14076171663391406153016587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9384114442260937435344391 14076171663391406153016587)
      ·
        refine ⟨21114257495087109229524881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14076171663391406153016587 21114257495087109229524881)
        ·
          refine ⟨15835693121315331922143661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21114257495087109229524881 15835693121315331922143661)
          ·
            refine ⟨5938384920493249470803873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15835693121315331922143661 5938384920493249470803873)
            ·
              refine ⟨4453788690369937103102905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938384920493249470803873 4453788690369937103102905)
              ·
                refine ⟨3340341517777452827327179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4453788690369937103102905 3340341517777452827327179)
                ·
                  refine ⟨5010512276666179240990769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340341517777452827327179 5010512276666179240990769)
                  ·
                    refine ⟨3757884207499634430743077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5010512276666179240990769 3757884207499634430743077)
                    ·
                      refine ⟨704603288906181455764327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3757884207499634430743077 704603288906181455764327)
                      ·
                        rfl

theorem cell23_1372210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1372210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372210 prefixEnd_1372210 := by exact prefixLift 1372210
  have htrace : WordTrace (prefixWord ++ tailWord_1372210) baseStart_1372210 baseEnd_1372210 := by
    simpa [prefixWord, tailWord_1372210, baseEnd_1372210] using wordTrace_append hprefix tailTrace_1372210
  have hstable : (prefixWord ++ tailWord_1372210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372210).length < 2 ^ (prefixWord ++ tailWord_1372210).sum := by decide
  have hdescent : baseEnd_1372210 < baseStart_1372210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372214 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_1372214 : Nat := 118140960795 + 1372214 * 2 ^ 59
def prefixEnd_1372214 : Nat := 4983230072969 + 3 ^ 40 * 1372214 * 2
def baseEnd_1372214 : Nat := 704605342828799440114309

theorem tailTrace_1372214 : CollatzResearch.WordTrace tailWord_1372214 prefixEnd_1372214 704605342828799440114309 := by
  unfold tailWord_1372214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128047265669406771144731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33365837500473672225543797 3128047265669406771144731)
  ·
    refine ⟨4692070898504110156717097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3128047265669406771144731 4692070898504110156717097)
    ·
      refine ⟨3519053173878082617537823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4692070898504110156717097 3519053173878082617537823)
      ·
        refine ⟨5278579760817123926306735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519053173878082617537823 5278579760817123926306735)
        ·
          refine ⟨7917869641225685889460103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278579760817123926306735 7917869641225685889460103)
          ·
            refine ⟨11876804461838528834190155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917869641225685889460103 11876804461838528834190155)
            ·
              refine ⟨17815206692757793251285233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11876804461838528834190155 17815206692757793251285233)
              ·
                refine ⟨13361405019568344938463925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17815206692757793251285233 13361405019568344938463925)
                ·
                  refine ⟨1252631720584532337980993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13361405019568344938463925 1252631720584532337980993)
                  ·
                    refine ⟨939473790438399253485745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1252631720584532337980993 939473790438399253485745)
                    ·
                      refine ⟨704605342828799440114309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939473790438399253485745 704605342828799440114309)
                      ·
                        rfl

theorem cell23_1372214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_1372214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372214 prefixEnd_1372214 := by exact prefixLift 1372214
  have htrace : WordTrace (prefixWord ++ tailWord_1372214) baseStart_1372214 baseEnd_1372214 := by
    simpa [prefixWord, tailWord_1372214, baseEnd_1372214] using wordTrace_append hprefix tailTrace_1372214
  have hstable : (prefixWord ++ tailWord_1372214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372214).length < 2 ^ (prefixWord ++ tailWord_1372214).sum := by decide
  have hdescent : baseEnd_1372214 < baseStart_1372214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372247 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_1372247 : Nat := 118140960795 + 1372247 * 2 ^ 59
def prefixEnd_1372247 : Nat := 4983230072969 + 3 ^ 40 * 1372247 * 2
def baseEnd_1372247 : Nat := 704622287690397811001657

theorem tailTrace_1372247 : CollatzResearch.WordTrace tailWord_1372247 prefixEnd_1372247 704622287690397811001657 := by
  unfold tailWord_1372247
  simp only [CollatzResearch.WordTrace]
  refine ⟨50049959859590954974266995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33366639906393969982844663 50049959859590954974266995)
  ·
    refine ⟨75074939789386432461400493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50049959859590954974266995 75074939789386432461400493)
    ·
      refine ⟨28153102421019912173025185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75074939789386432461400493 28153102421019912173025185)
      ·
        refine ⟨21114826815764934129768889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28153102421019912173025185 21114826815764934129768889)
        ·
          refine ⟨15836120111823700597326667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21114826815764934129768889 15836120111823700597326667)
          ·
            refine ⟨23754180167735550895990001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15836120111823700597326667 23754180167735550895990001)
            ·
              refine ⟨17815635125801663171992501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23754180167735550895990001 17815635125801663171992501)
              ·
                refine ⟨1670215793043905922374297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17815635125801663171992501 1670215793043905922374297)
                ·
                  refine ⟨1252661844782929441780723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1670215793043905922374297 1252661844782929441780723)
                  ·
                    refine ⟨1878992767174394162671085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252661844782929441780723 1878992767174394162671085)
                    ·
                      refine ⟨704622287690397811001657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878992767174394162671085 704622287690397811001657)
                      ·
                        rfl

theorem cell23_1372247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_1372247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372247 prefixEnd_1372247 := by exact prefixLift 1372247
  have htrace : WordTrace (prefixWord ++ tailWord_1372247) baseStart_1372247 baseEnd_1372247 := by
    simpa [prefixWord, tailWord_1372247, baseEnd_1372247] using wordTrace_append hprefix tailTrace_1372247
  have hstable : (prefixWord ++ tailWord_1372247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372247).length < 2 ^ (prefixWord ++ tailWord_1372247).sum := by decide
  have hdescent : baseEnd_1372247 < baseStart_1372247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372254 : List Nat := [4, 4, 1, 1, 2, 1, 1, 9]
def baseStart_1372254 : Nat := 118140960795 + 1372254 * 2 ^ 59
def prefixEnd_1372254 : Nat := 4983230072969 + 3 ^ 40 * 1372254 * 2
def baseEnd_1372254 : Nat := 26097254890925158652375

theorem tailTrace_1372254 : CollatzResearch.WordTrace tailWord_1372254 prefixEnd_1372254 26097254890925158652375 := by
  unfold tailWord_1372254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256276896320699396221477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33366810113710396779847877 6256276896320699396221477)
  ·
    refine ⟨1173051918060131136791527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6256276896320699396221477 1173051918060131136791527)
    ·
      refine ⟨1759577877090196705187291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1173051918060131136791527 1759577877090196705187291)
      ·
        refine ⟨2639366815635295057780937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759577877090196705187291 2639366815635295057780937)
        ·
          refine ⟨1979525111726471293335703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639366815635295057780937 1979525111726471293335703)
          ·
            refine ⟨2969287667589706940003555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979525111726471293335703 2969287667589706940003555)
            ·
              refine ⟨4453931501384560410005333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969287667589706940003555 4453931501384560410005333)
              ·
                refine ⟨26097254890925158652375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4453931501384560410005333 26097254890925158652375)
                ·
                  rfl

theorem cell23_1372254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_1372254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372254 prefixEnd_1372254 := by exact prefixLift 1372254
  have htrace : WordTrace (prefixWord ++ tailWord_1372254) baseStart_1372254 baseEnd_1372254 := by
    simpa [prefixWord, tailWord_1372254, baseEnd_1372254] using wordTrace_append hprefix tailTrace_1372254
  have hstable : (prefixWord ++ tailWord_1372254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372254).length < 2 ^ (prefixWord ++ tailWord_1372254).sum := by decide
  have hdescent : baseEnd_1372254 < baseStart_1372254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372274 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_1372274 : Nat := 118140960795 + 1372274 * 2 ^ 59
def prefixEnd_1372274 : Nat := 4983230072969 + 3 ^ 40 * 1372274 * 2
def baseEnd_1372274 : Nat := 704636151668069205364033

theorem tailTrace_1372274 : CollatzResearch.WordTrace tailWord_1372274 prefixEnd_1372274 704636151668069205364033 := by
  unfold tailWord_1372274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12512736157623284646374969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33367296420328759056999917 12512736157623284646374969)
  ·
    refine ⟨9384552118217463484781227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12512736157623284646374969 9384552118217463484781227)
    ·
      refine ⟨14076828177326195227171841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9384552118217463484781227 14076828177326195227171841)
      ·
        refine ⟨10557621132994646420378881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14076828177326195227171841 10557621132994646420378881)
        ·
          refine ⟨7918215849745984815284161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10557621132994646420378881 7918215849745984815284161)
          ·
            refine ⟨5938661887309488611463121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7918215849745984815284161 5938661887309488611463121)
            ·
              refine ⟨4453996415482116458597341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938661887309488611463121 4453996415482116458597341)
              ·
                refine ⟨1670248655805793671974003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4453996415482116458597341 1670248655805793671974003)
                ·
                  refine ⟨2505372983708690507961005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670248655805793671974003 2505372983708690507961005)
                  ·
                    refine ⟨939514868890758940485377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505372983708690507961005 939514868890758940485377)
                    ·
                      refine ⟨704636151668069205364033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939514868890758940485377 704636151668069205364033)
                      ·
                        rfl

theorem cell23_1372274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_1372274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372274 prefixEnd_1372274 := by exact prefixLift 1372274
  have htrace : WordTrace (prefixWord ++ tailWord_1372274) baseStart_1372274 baseEnd_1372274 := by
    simpa [prefixWord, tailWord_1372274, baseEnd_1372274] using wordTrace_append hprefix tailTrace_1372274
  have hstable : (prefixWord ++ tailWord_1372274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372274).length < 2 ^ (prefixWord ++ tailWord_1372274).sum := by decide
  have hdescent : baseEnd_1372274 < baseStart_1372274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372304 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 2, 2, 2]
def baseStart_1372304 : Nat := 118140960795 + 1372304 * 2 ^ 59
def prefixEnd_1372304 : Nat := 4983230072969 + 3 ^ 40 * 1372304 * 2
def baseEnd_1372304 : Nat := 704651556087704087988895

theorem tailTrace_1372304 : CollatzResearch.WordTrace tailWord_1372304 prefixEnd_1372304 704651556087704087988895 := by
  unfold tailWord_1372304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25026019410192226854545983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33368025880256302472727977 25026019410192226854545983)
  ·
    refine ⟨37539029115288340281818975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25026019410192226854545983 37539029115288340281818975)
    ·
      refine ⟨56308543672932510422728463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37539029115288340281818975 56308543672932510422728463)
      ·
        refine ⟨84462815509398765634092695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56308543672932510422728463 84462815509398765634092695)
        ·
          refine ⟨126694223264098148451139043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84462815509398765634092695 126694223264098148451139043)
          ·
            refine ⟨190041334896147222676708565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126694223264098148451139043 190041334896147222676708565)
            ·
              refine ⟨4454093786628450531485357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 190041334896147222676708565 4454093786628450531485357)
              ·
                refine ⟨1670285169985668949307009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4454093786628450531485357 1670285169985668949307009)
                ·
                  refine ⟨1252713877489251711980257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1670285169985668949307009 1252713877489251711980257)
                  ·
                    refine ⟨939535408116938783985193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1252713877489251711980257 939535408116938783985193)
                    ·
                      refine ⟨704651556087704087988895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939535408116938783985193 704651556087704087988895)
                      ·
                        rfl

theorem cell23_1372304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 2, 2].length) (baseStart_1372304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372304 prefixEnd_1372304 := by exact prefixLift 1372304
  have htrace : WordTrace (prefixWord ++ tailWord_1372304) baseStart_1372304 baseEnd_1372304 := by
    simpa [prefixWord, tailWord_1372304, baseEnd_1372304] using wordTrace_append hprefix tailTrace_1372304
  have hstable : (prefixWord ++ tailWord_1372304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372304).length < 2 ^ (prefixWord ++ tailWord_1372304).sum := by decide
  have hdescent : baseEnd_1372304 < baseStart_1372304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372313 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_1372313 : Nat := 118140960795 + 1372313 * 2 ^ 59
def prefixEnd_1372313 : Nat := 4983230072969 + 3 ^ 40 * 1372313 * 2
def baseEnd_1372313 : Nat := 704656177413594552776353

theorem tailTrace_1372313 : CollatzResearch.WordTrace tailWord_1372313 prefixEnd_1372313 704656177413594552776353 := by
  unfold tailWord_1372313
  simp only [CollatzResearch.WordTrace]
  refine ⟨50052367077351848246169593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33368244718234565497446395 50052367077351848246169593)
  ·
    refine ⟨37539275308013886184627195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50052367077351848246169593 37539275308013886184627195)
    ·
      refine ⟨56308912962020829276940793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37539275308013886184627195 56308912962020829276940793)
      ·
        refine ⟨42231684721515621957705595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56308912962020829276940793 42231684721515621957705595)
        ·
          refine ⟨63347527082273432936558393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42231684721515621957705595 63347527082273432936558393)
          ·
            refine ⟨47510645311705074702418795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63347527082273432936558393 47510645311705074702418795)
            ·
              refine ⟨71265967967557612053628193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47510645311705074702418795 71265967967557612053628193)
              ·
                refine ⟨53449475975668209040221145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71265967967557612053628193 53449475975668209040221145)
                ·
                  refine ⟨40087106981751156780165859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53449475975668209040221145 40087106981751156780165859)
                  ·
                    refine ⟨60130660472626735170248789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40087106981751156780165859 60130660472626735170248789)
                    ·
                      refine ⟨704656177413594552776353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 60130660472626735170248789 704656177413594552776353)
                      ·
                        rfl

theorem cell23_1372313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_1372313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372313 prefixEnd_1372313 := by exact prefixLift 1372313
  have htrace : WordTrace (prefixWord ++ tailWord_1372313) baseStart_1372313 baseEnd_1372313 := by
    simpa [prefixWord, tailWord_1372313, baseEnd_1372313] using wordTrace_append hprefix tailTrace_1372313
  have hstable : (prefixWord ++ tailWord_1372313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372313).length < 2 ^ (prefixWord ++ tailWord_1372313).sum := by decide
  have hdescent : baseEnd_1372313 < baseStart_1372313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372360 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_1372360 : Nat := 118140960795 + 1372360 * 2 ^ 59
def prefixEnd_1372360 : Nat := 4983230072969 + 3 ^ 40 * 1372360 * 2
def baseEnd_1372360 : Nat := 704680311004355868888637

theorem tailTrace_1372360 : CollatzResearch.WordTrace tailWord_1372360 prefixEnd_1372360 704680311004355868888637 := by
  unfold tailWord_1372360
  simp only [CollatzResearch.WordTrace]
  refine ⟨25027040654090787636565267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33369387538787716848753689 25027040654090787636565267)
  ·
    refine ⟨37540560981136181454847901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25027040654090787636565267 37540560981136181454847901)
    ·
      refine ⟨14077710367926068045567963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37540560981136181454847901 14077710367926068045567963)
      ·
        refine ⟨21116565551889102068351945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14077710367926068045567963 21116565551889102068351945)
        ·
          refine ⟨15837424163916826551263959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21116565551889102068351945 15837424163916826551263959)
          ·
            refine ⟨23756136245875239826895939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15837424163916826551263959 23756136245875239826895939)
            ·
              refine ⟨35634204368812859740343909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23756136245875239826895939 35634204368812859740343909)
              ·
                refine ⟨6681413319152411201314483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35634204368812859740343909 6681413319152411201314483)
                ·
                  refine ⟨10022119978728616801971725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6681413319152411201314483 10022119978728616801971725)
                  ·
                    refine ⟨3758294992023231300739397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10022119978728616801971725 3758294992023231300739397)
                    ·
                      refine ⟨704680311004355868888637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3758294992023231300739397 704680311004355868888637)
                      ·
                        rfl

theorem cell23_1372360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_1372360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372360 prefixEnd_1372360 := by exact prefixLift 1372360
  have htrace : WordTrace (prefixWord ++ tailWord_1372360) baseStart_1372360 baseEnd_1372360 := by
    simpa [prefixWord, tailWord_1372360, baseEnd_1372360] using wordTrace_append hprefix tailTrace_1372360
  have hstable : (prefixWord ++ tailWord_1372360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372360).length < 2 ^ (prefixWord ++ tailWord_1372360).sum := by decide
  have hdescent : baseEnd_1372360 < baseStart_1372360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372374 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1372374 : Nat := 118140960795 + 1372374 * 2 ^ 59
def prefixEnd_1372374 : Nat := 4983230072969 + 3 ^ 40 * 1372374 * 2
def baseEnd_1372374 : Nat := 234895833244506271371191

theorem tailTrace_1372374 : CollatzResearch.WordTrace tailWord_1372374 prefixEnd_1372374 234895833244506271371191 := by
  unfold tailWord_1372374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128411995633178479008761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33369727953420570442760117 3128411995633178479008761)
  ·
    refine ⟨2346308996724883859256571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3128411995633178479008761 2346308996724883859256571)
    ·
      refine ⟨3519463495087325788884857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346308996724883859256571 3519463495087325788884857)
      ·
        refine ⟨2639597621315494341663643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3519463495087325788884857 2639597621315494341663643)
        ·
          refine ⟨3959396431973241512495465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2639597621315494341663643 3959396431973241512495465)
          ·
            refine ⟨2969547323979931134371599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3959396431973241512495465 2969547323979931134371599)
            ·
              refine ⟨4454320985969896701557399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969547323979931134371599 4454320985969896701557399)
              ·
                refine ⟨6681481478954845052336099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454320985969896701557399 6681481478954845052336099)
                ·
                  refine ⟨10022222218432267578504149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6681481478954845052336099 10022222218432267578504149)
                  ·
                    refine ⟨234895833244506271371191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10022222218432267578504149 234895833244506271371191)
                    ·
                      rfl

theorem cell23_1372374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1372374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372374 prefixEnd_1372374 := by exact prefixLift 1372374
  have htrace : WordTrace (prefixWord ++ tailWord_1372374) baseStart_1372374 baseEnd_1372374 := by
    simpa [prefixWord, tailWord_1372374, baseEnd_1372374] using wordTrace_append hprefix tailTrace_1372374
  have hstable : (prefixWord ++ tailWord_1372374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372374).length < 2 ^ (prefixWord ++ tailWord_1372374).sum := by decide
  have hdescent : baseEnd_1372374 < baseStart_1372374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372377 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 4]
def baseStart_1372377 : Nat := 118140960795 + 1372377 * 2 ^ 59
def prefixEnd_1372377 : Nat := 4983230072969 + 3 ^ 40 * 1372377 * 2
def baseEnd_1372377 : Nat := 704689040175482302376059

theorem tailTrace_1372377 : CollatzResearch.WordTrace tailWord_1372377 prefixEnd_1372377 704689040175482302376059 := by
  unfold tailWord_1372377
  simp only [CollatzResearch.WordTrace]
  refine ⟨50054701349119987176499385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33369800899413324784332923 50054701349119987176499385)
  ·
    refine ⟨37541026011839990382374539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50054701349119987176499385 37541026011839990382374539)
    ·
      refine ⟨56311539017759985573561809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37541026011839990382374539 56311539017759985573561809)
      ·
        refine ⟨42233654263319989180171357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56311539017759985573561809 42233654263319989180171357)
        ·
          refine ⟨15837620348744995942564259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42233654263319989180171357 15837620348744995942564259)
          ·
            refine ⟨23756430523117493913846389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15837620348744995942564259 23756430523117493913846389)
            ·
              refine ⟨2227165361542265054423099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23756430523117493913846389 2227165361542265054423099)
              ·
                refine ⟨3340748042313397581634649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227165361542265054423099 3340748042313397581634649)
                ·
                  refine ⟨2505561031735048186225987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340748042313397581634649 2505561031735048186225987)
                  ·
                    refine ⟨3758341547602572279338981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2505561031735048186225987 3758341547602572279338981)
                    ·
                      refine ⟨704689040175482302376059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3758341547602572279338981 704689040175482302376059)
                      ·
                        rfl

theorem cell23_1372377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_1372377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372377 prefixEnd_1372377 := by exact prefixLift 1372377
  have htrace : WordTrace (prefixWord ++ tailWord_1372377) baseStart_1372377 baseEnd_1372377 := by
    simpa [prefixWord, tailWord_1372377, baseEnd_1372377] using wordTrace_append hprefix tailTrace_1372377
  have hstable : (prefixWord ++ tailWord_1372377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372377).length < 2 ^ (prefixWord ++ tailWord_1372377).sum := by decide
  have hdescent : baseEnd_1372377 < baseStart_1372377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372455 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1372455 : Nat := 118140960795 + 1372455 * 2 ^ 59
def prefixEnd_1372455 : Nat := 4983230072969 + 3 ^ 40 * 1372455 * 2
def baseEnd_1372455 : Nat := 234909697222177665733567

theorem tailTrace_1372455 : CollatzResearch.WordTrace tailWord_1372455 prefixEnd_1372455 234909697222177665733567 := by
  unfold tailWord_1372455
  simp only [CollatzResearch.WordTrace]
  refine ⟨50057546242837406497838819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33371697495224937665225879 50057546242837406497838819)
  ·
    refine ⟨75086319364256109746758229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50057546242837406497838819 75086319364256109746758229)
    ·
      refine ⟨879917805049876286094823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 75086319364256109746758229 879917805049876286094823)
      ·
        refine ⟨1319876707574814429142235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879917805049876286094823 1319876707574814429142235)
        ·
          refine ⟨1979815061362221643713353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319876707574814429142235 1979815061362221643713353)
          ·
            refine ⟨1484861296021666232785015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1979815061362221643713353 1484861296021666232785015)
            ·
              refine ⟨2227291944032499349177523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484861296021666232785015 2227291944032499349177523)
              ·
                refine ⟨3340937916048749023766285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227291944032499349177523 3340937916048749023766285)
                ·
                  refine ⟨1252851718518280883912357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3340937916048749023766285 1252851718518280883912357)
                  ·
                    refine ⟨234909697222177665733567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1252851718518280883912357 234909697222177665733567)
                    ·
                      rfl

theorem cell23_1372455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1372455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372455 prefixEnd_1372455 := by exact prefixLift 1372455
  have htrace : WordTrace (prefixWord ++ tailWord_1372455) baseStart_1372455 baseEnd_1372455 := by
    simpa [prefixWord, tailWord_1372455, baseEnd_1372455] using wordTrace_append hprefix tailTrace_1372455
  have hstable : (prefixWord ++ tailWord_1372455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372455).length < 2 ^ (prefixWord ++ tailWord_1372455).sum := by decide
  have hdescent : baseEnd_1372455 < baseStart_1372455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372467 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 4]
def baseStart_1372467 : Nat := 118140960795 + 1372467 * 2 ^ 59
def prefixEnd_1372467 : Nat := 4983230072969 + 3 ^ 40 * 1372467 * 2
def baseEnd_1372467 : Nat := 704735253434386950250645

theorem tailTrace_1372467 : CollatzResearch.WordTrace tailWord_1372467 prefixEnd_1372467 704735253434386950250645 := by
  unfold tailWord_1372467
  simp only [CollatzResearch.WordTrace]
  refine ⟨50057983918793932547275655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33371989279195955031517103 50057983918793932547275655)
  ·
    refine ⟨75086975878190898820913483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50057983918793932547275655 75086975878190898820913483)
    ·
      refine ⟨112630463817286348231370225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75086975878190898820913483 112630463817286348231370225)
      ·
        refine ⟨84472847862964761173527669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112630463817286348231370225 84472847862964761173527669)
        ·
          refine ⟨7919329487152946360018219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84472847862964761173527669 7919329487152946360018219)
          ·
            refine ⟨11878994230729419540027329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7919329487152946360018219 11878994230729419540027329)
            ·
              refine ⟨8909245673047064655020497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11878994230729419540027329 8909245673047064655020497)
              ·
                refine ⟨6681934254785298491265373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8909245673047064655020497 6681934254785298491265373)
                ·
                  refine ⟨2505725345544486934224515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6681934254785298491265373 2505725345544486934224515)
                  ·
                    refine ⟨3758588018316730401336773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2505725345544486934224515 3758588018316730401336773)
                    ·
                      refine ⟨704735253434386950250645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3758588018316730401336773 704735253434386950250645)
                      ·
                        rfl

theorem cell23_1372467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_1372467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372467 prefixEnd_1372467 := by exact prefixLift 1372467
  have htrace : WordTrace (prefixWord ++ tailWord_1372467) baseStart_1372467 baseEnd_1372467 := by
    simpa [prefixWord, tailWord_1372467, baseEnd_1372467] using wordTrace_append hprefix tailTrace_1372467
  have hstable : (prefixWord ++ tailWord_1372467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372467).length < 2 ^ (prefixWord ++ tailWord_1372467).sum := by decide
  have hdescent : baseEnd_1372467 < baseStart_1372467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372497 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_1372497 : Nat := 118140960795 + 1372497 * 2 ^ 59
def prefixEnd_1372497 : Nat := 4983230072969 + 3 ^ 40 * 1372497 * 2
def baseEnd_1372497 : Nat := 704750657854021832875507

theorem tailTrace_1372497 : CollatzResearch.WordTrace tailWord_1372497 prefixEnd_1372497 704750657854021832875507 := by
  unfold tailWord_1372497
  simp only [CollatzResearch.WordTrace]
  refine ⟨50059078108685247670867745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33372718739123498447245163 50059078108685247670867745)
  ·
    refine ⟨37544308581513935753150809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50059078108685247670867745 37544308581513935753150809)
    ·
      refine ⟨28158231436135451814863107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37544308581513935753150809 28158231436135451814863107)
      ·
        refine ⟨42237347154203177722294661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28158231436135451814863107 42237347154203177722294661)
        ·
          refine ⟨7919502591413095822930249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42237347154203177722294661 7919502591413095822930249)
          ·
            refine ⟨5939626943559821867197687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7919502591413095822930249 5939626943559821867197687)
            ·
              refine ⟨8909440415339732800796531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939626943559821867197687 8909440415339732800796531)
              ·
                refine ⟨13364160623009599201194797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8909440415339732800796531 13364160623009599201194797)
                ·
                  refine ⟨5011560233628599700448049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13364160623009599201194797 5011560233628599700448049)
                  ·
                    refine ⟨3758670175221449775336037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5011560233628599700448049 3758670175221449775336037)
                    ·
                      refine ⟨704750657854021832875507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3758670175221449775336037 704750657854021832875507)
                      ·
                        rfl

theorem cell23_1372497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_1372497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372497 prefixEnd_1372497 := by exact prefixLift 1372497
  have htrace : WordTrace (prefixWord ++ tailWord_1372497) baseStart_1372497 baseEnd_1372497 := by
    simpa [prefixWord, tailWord_1372497, baseEnd_1372497] using wordTrace_append hprefix tailTrace_1372497
  have hstable : (prefixWord ++ tailWord_1372497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372497).length < 2 ^ (prefixWord ++ tailWord_1372497).sum := by decide
  have hdescent : baseEnd_1372497 < baseStart_1372497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372512 : List Nat := [2, 1, 1, 3, 6, 1, 2, 2, 1, 1, 3]
def baseStart_1372512 : Nat := 118140960795 + 1372512 * 2 ^ 59
def prefixEnd_1372512 : Nat := 4983230072969 + 3 ^ 40 * 1372512 * 2
def baseEnd_1372512 : Nat := 704758360063839274187939

theorem tailTrace_1372512 : CollatzResearch.WordTrace tailWord_1372512 prefixEnd_1372512 704758360063839274187939 := by
  unfold tailWord_1372512
  simp only [CollatzResearch.WordTrace]
  refine ⟨25029812601815452616331895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33373083469087270155109193 25029812601815452616331895)
  ·
    refine ⟨37544718902723178924497843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25029812601815452616331895 37544718902723178924497843)
    ·
      refine ⟨56317078354084768386746765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37544718902723178924497843 56317078354084768386746765)
      ·
        refine ⟨21118904382781788145030037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56317078354084768386746765 21118904382781788145030037)
        ·
          refine ⟨989948642942896319298283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21118904382781788145030037 989948642942896319298283)
          ·
            refine ⟨1484922964414344478947425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989948642942896319298283 1484922964414344478947425)
            ·
              refine ⟨1113692223310758359210569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1484922964414344478947425 1113692223310758359210569)
              ·
                refine ⟨835269167483068769407927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113692223310758359210569 835269167483068769407927)
                ·
                  refine ⟨1252903751224603154111891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835269167483068769407927 1252903751224603154111891)
                  ·
                    refine ⟨1879355626836904731167837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252903751224603154111891 1879355626836904731167837)
                    ·
                      refine ⟨704758360063839274187939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1879355626836904731167837 704758360063839274187939)
                      ·
                        rfl

theorem cell23_1372512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_1372512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372512 prefixEnd_1372512 := by exact prefixLift 1372512
  have htrace : WordTrace (prefixWord ++ tailWord_1372512) baseStart_1372512 baseEnd_1372512 := by
    simpa [prefixWord, tailWord_1372512, baseEnd_1372512] using wordTrace_append hprefix tailTrace_1372512
  have hstable : (prefixWord ++ tailWord_1372512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372512).length < 2 ^ (prefixWord ++ tailWord_1372512).sum := by decide
  have hdescent : baseEnd_1372512 < baseStart_1372512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372524 : List Nat := [2, 2, 1, 1, 6, 2, 1, 8]
def baseStart_1372524 : Nat := 118140960795 + 1372524 * 2 ^ 59
def prefixEnd_1372524 : Nat := 4983230072969 + 3 ^ 40 * 1372524 * 2
def baseEnd_1372524 : Nat := 26102389697470119527329

theorem tailTrace_1372524 : CollatzResearch.WordTrace tailWord_1372524 prefixEnd_1372524 26102389697470119527329 := by
  unfold tailWord_1372524
  simp only [CollatzResearch.WordTrace]
  refine ⟨25030031439793715641050313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33373375253058287521400417 25030031439793715641050313)
  ·
    refine ⟨18772523579845286730787735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25030031439793715641050313 18772523579845286730787735)
    ·
      refine ⟨28158785369767930096181603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18772523579845286730787735 28158785369767930096181603)
      ·
        refine ⟨42238178054651895144272405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28158785369767930096181603 42238178054651895144272405)
        ·
          refine ⟨1979914596311807584887769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42238178054651895144272405 1979914596311807584887769)
          ·
            refine ⟨1484935947233855688665827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1979914596311807584887769 1484935947233855688665827)
            ·
              refine ⟨2227403920850783532998741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484935947233855688665827 2227403920850783532998741)
              ·
                refine ⟨26102389697470119527329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2227403920850783532998741 26102389697470119527329)
                ·
                  rfl

theorem cell23_1372524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 8].length) (baseStart_1372524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372524 prefixEnd_1372524 := by exact prefixLift 1372524
  have htrace : WordTrace (prefixWord ++ tailWord_1372524) baseStart_1372524 baseEnd_1372524 := by
    simpa [prefixWord, tailWord_1372524, baseEnd_1372524] using wordTrace_append hprefix tailTrace_1372524
  have hstable : (prefixWord ++ tailWord_1372524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372524).length < 2 ^ (prefixWord ++ tailWord_1372524).sum := by decide
  have hdescent : baseEnd_1372524 < baseStart_1372524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372567 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 2, 6]
def baseStart_1372567 : Nat := 118140960795 + 1372567 * 2 ^ 59
def prefixEnd_1372567 : Nat := 4983230072969 + 3 ^ 40 * 1372567 * 2
def baseEnd_1372567 : Nat := 234928867166612186333395

theorem tailTrace_1372567 : CollatzResearch.WordTrace tailWord_1372567 prefixEnd_1372567 234928867166612186333395 := by
  unfold tailWord_1372567
  simp only [CollatzResearch.WordTrace]
  refine ⟨50061631218431649625915955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33374420812287766417277303 50061631218431649625915955)
  ·
    refine ⟨75092446827647474438873933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50061631218431649625915955 75092446827647474438873933)
    ·
      refine ⟨28159667560367802914577725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75092446827647474438873933 28159667560367802914577725)
      ·
        refine ⟨10559875335137926092966647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28159667560367802914577725 10559875335137926092966647)
        ·
          refine ⟨15839813002706889139449971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10559875335137926092966647 15839813002706889139449971)
          ·
            refine ⟨23759719504060333709174957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15839813002706889139449971 23759719504060333709174957)
            ·
              refine ⟨8909894814022625140940609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23759719504060333709174957 8909894814022625140940609)
              ·
                refine ⟨6682421110516968855705457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8909894814022625140940609 6682421110516968855705457)
                ·
                  refine ⟨5011815832887726641779093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6682421110516968855705457 5011815832887726641779093)
                  ·
                    refine ⟨234928867166612186333395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5011815832887726641779093 234928867166612186333395)
                    ·
                      rfl

theorem cell23_1372567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_1372567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372567 prefixEnd_1372567 := by exact prefixLift 1372567
  have htrace : WordTrace (prefixWord ++ tailWord_1372567) baseStart_1372567 baseEnd_1372567 := by
    simpa [prefixWord, tailWord_1372567, baseEnd_1372567] using wordTrace_append hprefix tailTrace_1372567
  have hstable : (prefixWord ++ tailWord_1372567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372567).length < 2 ^ (prefixWord ++ tailWord_1372567).sum := by decide
  have hdescent : baseEnd_1372567 < baseStart_1372567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372568 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1372568 : Nat := 118140960795 + 1372568 * 2 ^ 59
def prefixEnd_1372568 : Nat := 4983230072969 + 3 ^ 40 * 1372568 * 2
def baseEnd_1372568 : Nat := 704787114980491055087681

theorem tailTrace_1372568 : CollatzResearch.WordTrace tailWord_1372568 prefixEnd_1372568 704787114980491055087681 := by
  unfold tailWord_1372568
  simp only [CollatzResearch.WordTrace]
  refine ⟨25030833845714013398351179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33374445127618684531134905 25030833845714013398351179)
  ·
    refine ⟨37546250768571020097526769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25030833845714013398351179 37546250768571020097526769)
    ·
      refine ⟨28159688076428265073145077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37546250768571020097526769 28159688076428265073145077)
      ·
        refine ⟨2639970757165149850607351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28159688076428265073145077 2639970757165149850607351)
        ·
          refine ⟨3959956135747724775911027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2639970757165149850607351 3959956135747724775911027)
          ·
            refine ⟨5939934203621587163866541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959956135747724775911027 5939934203621587163866541)
            ·
              refine ⟨2227475326358095186449953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5939934203621587163866541 2227475326358095186449953)
              ·
                refine ⟨1670606494768571389837465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2227475326358095186449953 1670606494768571389837465)
                ·
                  refine ⟨1252954871076428542378099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1670606494768571389837465 1252954871076428542378099)
                  ·
                    refine ⟨1879432306614642813567149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252954871076428542378099 1879432306614642813567149)
                    ·
                      refine ⟨704787114980491055087681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1879432306614642813567149 704787114980491055087681)
                      ·
                        rfl

theorem cell23_1372568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1372568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372568 prefixEnd_1372568 := by exact prefixLift 1372568
  have htrace : WordTrace (prefixWord ++ tailWord_1372568) baseStart_1372568 baseEnd_1372568 := by
    simpa [prefixWord, tailWord_1372568, baseEnd_1372568] using wordTrace_append hprefix tailTrace_1372568
  have hstable : (prefixWord ++ tailWord_1372568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372568).length < 2 ^ (prefixWord ++ tailWord_1372568).sum := by decide
  have hdescent : baseEnd_1372568 < baseStart_1372568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372667 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 5]
def baseStart_1372667 : Nat := 118140960795 + 1372667 * 2 ^ 59
def prefixEnd_1372667 : Nat := 4983230072969 + 3 ^ 40 * 1372667 * 2
def baseEnd_1372667 : Nat := 704837949565286167749725

theorem tailTrace_1372667 : CollatzResearch.WordTrace tailWord_1372667 prefixEnd_1372667 704837949565286167749725 := by
  unfold tailWord_1372667
  simp only [CollatzResearch.WordTrace]
  refine ⟨50065278518069366704556255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33376852345379577803037503 50065278518069366704556255)
  ·
    refine ⟨75097917777104050056834383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50065278518069366704556255 75097917777104050056834383)
    ·
      refine ⟨112646876665656075085251575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75097917777104050056834383 112646876665656075085251575)
      ·
        refine ⟨168970314998484112627877363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112646876665656075085251575 168970314998484112627877363)
        ·
          refine ⟨253455472497726168941816045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168970314998484112627877363 253455472497726168941816045)
          ·
            refine ⟨95045802186647313353181017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253455472497726168941816045 95045802186647313353181017)
            ·
              refine ⟨71284351639985485014885763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95045802186647313353181017 71284351639985485014885763)
              ·
                refine ⟨106926527459978227522328645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71284351639985485014885763 106926527459978227522328645)
                ·
                  refine ⟨20048723898745917660436621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106926527459978227522328645 20048723898745917660436621)
                  ·
                    refine ⟨7518271462029719122663733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20048723898745917660436621 7518271462029719122663733)
                    ·
                      refine ⟨704837949565286167749725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7518271462029719122663733 704837949565286167749725)
                      ·
                        rfl

theorem cell23_1372667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_1372667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372667 prefixEnd_1372667 := by exact prefixLift 1372667
  have htrace : WordTrace (prefixWord ++ tailWord_1372667) baseStart_1372667 baseEnd_1372667 := by
    simpa [prefixWord, tailWord_1372667, baseEnd_1372667] using wordTrace_append hprefix tailTrace_1372667
  have hstable : (prefixWord ++ tailWord_1372667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372667).length < 2 ^ (prefixWord ++ tailWord_1372667).sum := by decide
  have hdescent : baseEnd_1372667 < baseStart_1372667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372685 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1372685 : Nat := 118140960795 + 1372685 * 2 ^ 59
def prefixEnd_1372685 : Nat := 4983230072969 + 3 ^ 40 * 1372685 * 2
def baseEnd_1372685 : Nat := 704847192217067097324643

theorem tailTrace_1372685 : CollatzResearch.WordTrace tailWord_1372685 prefixEnd_1372685 704847192217067097324643 := by
  unfold tailWord_1372685
  simp only [CollatzResearch.WordTrace]
  refine ⟨50065935032004155778711509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33377290021336103852474339 50065935032004155778711509)
  ·
    refine ⟨1173420352312597401063551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50065935032004155778711509 1173420352312597401063551)
    ·
      refine ⟨1760130528468896101595327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1173420352312597401063551 1760130528468896101595327)
      ·
        refine ⟨2640195792703344152392991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760130528468896101595327 2640195792703344152392991)
        ·
          refine ⟨3960293689055016228589487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640195792703344152392991 3960293689055016228589487)
          ·
            refine ⟨5940440533582524342884231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960293689055016228589487 5940440533582524342884231)
            ·
              refine ⟨8910660800373786514326347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5940440533582524342884231 8910660800373786514326347)
              ·
                refine ⟨13365991200560679771489521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8910660800373786514326347 13365991200560679771489521)
                ·
                  refine ⟨10024493400420509828617141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13365991200560679771489521 10024493400420509828617141)
                  ·
                    refine ⟨939796256289422796432857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10024493400420509828617141 939796256289422796432857)
                    ·
                      refine ⟨704847192217067097324643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939796256289422796432857 704847192217067097324643)
                      ·
                        rfl

theorem cell23_1372685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1372685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372685 prefixEnd_1372685 := by exact prefixLift 1372685
  have htrace : WordTrace (prefixWord ++ tailWord_1372685) baseStart_1372685 baseEnd_1372685 := by
    simpa [prefixWord, tailWord_1372685, baseEnd_1372685] using wordTrace_append hprefix tailTrace_1372685
  have hstable : (prefixWord ++ tailWord_1372685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372685).length < 2 ^ (prefixWord ++ tailWord_1372685).sum := by decide
  have hdescent : baseEnd_1372685 < baseStart_1372685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372718 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1372718 : Nat := 118140960795 + 1372718 * 2 ^ 59
def prefixEnd_1372718 : Nat := 4983230072969 + 3 ^ 40 * 1372718 * 2
def baseEnd_1372718 : Nat := 704864137078665468211991

theorem tailTrace_1372718 : CollatzResearch.WordTrace tailWord_1372718 prefixEnd_1372718 704864137078665468211991 := by
  unfold tailWord_1372718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6258392330110575301832851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33378092427256401609775205 6258392330110575301832851)
  ·
    refine ⟨9387588495165862952749277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6258392330110575301832851 9387588495165862952749277)
    ·
      refine ⟨3520345685687198607280979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9387588495165862952749277 3520345685687198607280979)
      ·
        refine ⟨5280518528530797910921469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520345685687198607280979 5280518528530797910921469)
        ·
          refine ⟨1980194448199049216595551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5280518528530797910921469 1980194448199049216595551)
          ·
            refine ⟨2970291672298573824893327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980194448199049216595551 2970291672298573824893327)
            ·
              refine ⟨4455437508447860737339991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970291672298573824893327 4455437508447860737339991)
              ·
                refine ⟨6683156262671791106009987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455437508447860737339991 6683156262671791106009987)
                ·
                  refine ⟨10024734394007686659014981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683156262671791106009987 10024734394007686659014981)
                  ·
                    refine ⟨1879637698876441248565309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10024734394007686659014981 1879637698876441248565309)
                    ·
                      refine ⟨704864137078665468211991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1879637698876441248565309 704864137078665468211991)
                      ·
                        rfl

theorem cell23_1372718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1372718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372718 prefixEnd_1372718 := by exact prefixLift 1372718
  have htrace : WordTrace (prefixWord ++ tailWord_1372718) baseStart_1372718 baseEnd_1372718 := by
    simpa [prefixWord, tailWord_1372718, baseEnd_1372718] using wordTrace_append hprefix tailTrace_1372718
  have hstable : (prefixWord ++ tailWord_1372718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372718).length < 2 ^ (prefixWord ++ tailWord_1372718).sum := by decide
  have hdescent : baseEnd_1372718 < baseStart_1372718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372742 : List Nat := [6, 1, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1372742 : Nat := 118140960795 + 1372742 * 2 ^ 59
def prefixEnd_1372742 : Nat := 4983230072969 + 3 ^ 40 * 1372742 * 2
def baseEnd_1372742 : Nat := 234958820204791124770627

theorem tailTrace_1372742 : CollatzResearch.WordTrace tailWord_1372742 prefixEnd_1372742 234958820204791124770627 := by
  unfold tailWord_1372742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564625437274926703548015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33378675995198436342357653 1564625437274926703548015)
  ·
    refine ⟨2346938155912390055322023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1564625437274926703548015 2346938155912390055322023)
    ·
      refine ⟨3520407233868585082983035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346938155912390055322023 3520407233868585082983035)
      ·
        refine ⟨5280610850802877624474553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520407233868585082983035 5280610850802877624474553)
        ·
          refine ⟨3960458138102158218355915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5280610850802877624474553 3960458138102158218355915)
          ·
            refine ⟨5940687207153237327533873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960458138102158218355915 5940687207153237327533873)
            ·
              refine ⟨4455515405364927995650405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5940687207153237327533873 4455515405364927995650405)
              ·
                refine ⟨835409138505923999184451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4455515405364927995650405 835409138505923999184451)
                ·
                  refine ⟨1253113707758885998776677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835409138505923999184451 1253113707758885998776677)
                  ·
                    refine ⟨234958820204791124770627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1253113707758885998776677 234958820204791124770627)
                    ·
                      rfl

theorem cell23_1372742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1372742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372742 prefixEnd_1372742 := by exact prefixLift 1372742
  have htrace : WordTrace (prefixWord ++ tailWord_1372742) baseStart_1372742 baseEnd_1372742 := by
    simpa [prefixWord, tailWord_1372742, baseEnd_1372742] using wordTrace_append hprefix tailTrace_1372742
  have hstable : (prefixWord ++ tailWord_1372742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372742).length < 2 ^ (prefixWord ++ tailWord_1372742).sum := by decide
  have hdescent : baseEnd_1372742 < baseStart_1372742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372748 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1372748 : Nat := 118140960795 + 1372748 * 2 ^ 59
def prefixEnd_1372748 : Nat := 4983230072969 + 3 ^ 40 * 1372748 * 2
def baseEnd_1372748 : Nat := 704879541498300350836853

theorem tailTrace_1372748 : CollatzResearch.WordTrace tailWord_1372748 prefixEnd_1372748 704879541498300350836853 := by
  unfold tailWord_1372748
  simp only [CollatzResearch.WordTrace]
  refine ⟨25034116415387958769127449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33378821887183945025503265 25034116415387958769127449)
  ·
    refine ⟨18775587311540969076845587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25034116415387958769127449 18775587311540969076845587)
    ·
      refine ⟨28163380967311453615268381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18775587311540969076845587 28163380967311453615268381)
      ·
        refine ⟨10561267862741795105725643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28163380967311453615268381 10561267862741795105725643)
        ·
          refine ⟨15841901794112692658588465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10561267862741795105725643 15841901794112692658588465)
          ·
            refine ⟨11881426345584519493941349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15841901794112692658588465 11881426345584519493941349)
            ·
              refine ⟨2227767439797097405114003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11881426345584519493941349 2227767439797097405114003)
              ·
                refine ⟨3341651159695646107671005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227767439797097405114003 3341651159695646107671005)
                ·
                  refine ⟨1253119184885867290376627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3341651159695646107671005 1253119184885867290376627)
                  ·
                    refine ⟨1879678777328800935564941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1253119184885867290376627 1879678777328800935564941)
                    ·
                      refine ⟨704879541498300350836853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1879678777328800935564941 704879541498300350836853)
                      ·
                        rfl

theorem cell23_1372748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1372748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372748 prefixEnd_1372748 := by exact prefixLift 1372748
  have htrace : WordTrace (prefixWord ++ tailWord_1372748) baseStart_1372748 baseEnd_1372748 := by
    simpa [prefixWord, tailWord_1372748, baseEnd_1372748] using wordTrace_append hprefix tailTrace_1372748
  have hstable : (prefixWord ++ tailWord_1372748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372748).length < 2 ^ (prefixWord ++ tailWord_1372748).sum := by decide
  have hdescent : baseEnd_1372748 < baseStart_1372748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372771 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 2, 6, 2]
def baseStart_1372771 : Nat := 118140960795 + 1372771 * 2 ^ 59
def prefixEnd_1372771 : Nat := 4983230072969 + 3 ^ 40 * 1372771 * 2
def baseEnd_1372771 : Nat := 704891351553353760849247

theorem tailTrace_1372771 : CollatzResearch.WordTrace tailWord_1372771 prefixEnd_1372771 704891351553353760849247 := by
  unfold tailWord_1372771
  simp only [CollatzResearch.WordTrace]
  refine ⟨50069071709692592466342167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33379381139795061644228111 50069071709692592466342167)
  ·
    refine ⟨75103607564538888699513251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50069071709692592466342167 75103607564538888699513251)
    ·
      refine ⟨112655411346808333049269877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75103607564538888699513251 112655411346808333049269877)
      ·
        refine ⟨10561444813763281223369051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112655411346808333049269877 10561444813763281223369051)
        ·
          refine ⟨15842167220644921835053577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10561444813763281223369051 15842167220644921835053577)
          ·
            refine ⟨11881625415483691376290183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15842167220644921835053577 11881625415483691376290183)
            ·
              refine ⟨17822438123225537064435275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11881625415483691376290183 17822438123225537064435275)
              ·
                refine ⟨26733657184838305596652913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17822438123225537064435275 26733657184838305596652913)
                ·
                  refine ⟨20050242888628729197489685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26733657184838305596652913 20050242888628729197489685)
                  ·
                    refine ⟨939855135404471681132329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20050242888628729197489685 939855135404471681132329)
                    ·
                      refine ⟨704891351553353760849247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939855135404471681132329 704891351553353760849247)
                      ·
                        rfl

theorem cell23_1372771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_1372771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372771 prefixEnd_1372771 := by exact prefixLift 1372771
  have htrace : WordTrace (prefixWord ++ tailWord_1372771) baseStart_1372771 baseEnd_1372771 := by
    simpa [prefixWord, tailWord_1372771, baseEnd_1372771] using wordTrace_append hprefix tailTrace_1372771
  have hstable : (prefixWord ++ tailWord_1372771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372771).length < 2 ^ (prefixWord ++ tailWord_1372771).sum := by decide
  have hdescent : baseEnd_1372771 < baseStart_1372771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372782 : List Nat := [4, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_1372782 : Nat := 118140960795 + 1372782 * 2 ^ 59
def prefixEnd_1372782 : Nat := 4983230072969 + 3 ^ 40 * 1372782 * 2
def baseEnd_1372782 : Nat := 704896999840553217811697

theorem tailTrace_1372782 : CollatzResearch.WordTrace tailWord_1372782 prefixEnd_1372782 704896999840553217811697 := by
  unfold tailWord_1372782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6258684114081592668124075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33379648608435160896661733 6258684114081592668124075)
  ·
    refine ⟨9388026171122389002186113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6258684114081592668124075 9388026171122389002186113)
    ·
      refine ⟨7041019628341791751639585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9388026171122389002186113 7041019628341791751639585)
      ·
        refine ⟨5280764721256343813729689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7041019628341791751639585 5280764721256343813729689)
        ·
          refine ⟨3960573540942257860297267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5280764721256343813729689 3960573540942257860297267)
          ·
            refine ⟨5940860311413386790445901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960573540942257860297267 5940860311413386790445901)
            ·
              refine ⟨2227822616780020046417213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5940860311413386790445901 2227822616780020046417213)
              ·
                refine ⟨835433481292507517406455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2227822616780020046417213 835433481292507517406455)
                ·
                  refine ⟨1253150221938761276109683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835433481292507517406455 1253150221938761276109683)
                  ·
                    refine ⟨1879725332908141914164525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1253150221938761276109683 1879725332908141914164525)
                    ·
                      refine ⟨704896999840553217811697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1879725332908141914164525 704896999840553217811697)
                      ·
                        rfl

theorem cell23_1372782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_1372782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372782 prefixEnd_1372782 := by exact prefixLift 1372782
  have htrace : WordTrace (prefixWord ++ tailWord_1372782) baseStart_1372782 baseEnd_1372782 := by
    simpa [prefixWord, tailWord_1372782, baseEnd_1372782] using wordTrace_append hprefix tailTrace_1372782
  have hstable : (prefixWord ++ tailWord_1372782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372782).length < 2 ^ (prefixWord ++ tailWord_1372782).sum := by decide
  have hdescent : baseEnd_1372782 < baseStart_1372782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372805 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 3, 2, 2]
def baseStart_1372805 : Nat := 118140960795 + 1372805 * 2 ^ 59
def prefixEnd_1372805 : Nat := 4983230072969 + 3 ^ 40 * 1372805 * 2
def baseEnd_1372805 : Nat := 704908809895606627824091

theorem tailTrace_1372805 : CollatzResearch.WordTrace tailWord_1372805 prefixEnd_1372805 704908809895606627824091 := by
  unfold tailWord_1372805
  simp only [CollatzResearch.WordTrace]
  refine ⟨50070311791569416273079869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33380207861046277515386579 50070311791569416273079869)
  ·
    refine ⟨18776366921838531102404951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50070311791569416273079869 18776366921838531102404951)
    ·
      refine ⟨28164550382757796653607427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18776366921838531102404951 28164550382757796653607427)
      ·
        refine ⟨42246825574136694980411141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28164550382757796653607427 42246825574136694980411141)
        ·
          refine ⟨7921279795150630308827089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42246825574136694980411141 7921279795150630308827089)
          ·
            refine ⟨5940959846362972731620317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7921279795150630308827089 5940959846362972731620317)
            ·
              refine ⟨2227859942386114774357619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5940959846362972731620317 2227859942386114774357619)
              ·
                refine ⟨3341789913579172161536429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227859942386114774357619 3341789913579172161536429)
                ·
                  refine ⟨1253171217592189560576161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3341789913579172161536429 1253171217592189560576161)
                  ·
                    refine ⟨939878413194142170432121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1253171217592189560576161 939878413194142170432121)
                    ·
                      refine ⟨704908809895606627824091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939878413194142170432121 704908809895606627824091)
                      ·
                        rfl

theorem cell23_1372805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_1372805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372805 prefixEnd_1372805 := by exact prefixLift 1372805
  have htrace : WordTrace (prefixWord ++ tailWord_1372805) baseStart_1372805 baseEnd_1372805 := by
    simpa [prefixWord, tailWord_1372805, baseEnd_1372805] using wordTrace_append hprefix tailTrace_1372805
  have hstable : (prefixWord ++ tailWord_1372805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372805).length < 2 ^ (prefixWord ++ tailWord_1372805).sum := by decide
  have hdescent : baseEnd_1372805 < baseStart_1372805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372842 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1372842 : Nat := 118140960795 + 1372842 * 2 ^ 59
def prefixEnd_1372842 : Nat := 4983230072969 + 3 ^ 40 * 1372842 * 2
def baseEnd_1372842 : Nat := 704927808679822983061421

theorem tailTrace_1372842 : CollatzResearch.WordTrace tailWord_1372842 prefixEnd_1372842 704927808679822983061421 := by
  unfold tailWord_1372842
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517915323108842898044195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33381107528290247728117853 12517915323108842898044195)
  ·
    refine ⟨18776872984663264347066293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12517915323108842898044195 18776872984663264347066293)
    ·
      refine ⟨1760331842312181032537465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18776872984663264347066293 1760331842312181032537465)
      ·
        refine ⟨1320248881734135774403099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1760331842312181032537465 1320248881734135774403099)
        ·
          refine ⟨1980373322601203661604649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320248881734135774403099 1980373322601203661604649)
          ·
            refine ⟨1485279991950902746203487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1980373322601203661604649 1485279991950902746203487)
            ·
              refine ⟨2227919987926354119305231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485279991950902746203487 2227919987926354119305231)
              ·
                refine ⟨3341879981889531178957847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227919987926354119305231 3341879981889531178957847)
                ·
                  refine ⟨5012819972834296768436771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341879981889531178957847 5012819972834296768436771)
                  ·
                    refine ⟨7519229959251445152655157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5012819972834296768436771 7519229959251445152655157)
                    ·
                      refine ⟨704927808679822983061421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7519229959251445152655157 704927808679822983061421)
                      ·
                        rfl

theorem cell23_1372842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1372842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372842 prefixEnd_1372842 := by exact prefixLift 1372842
  have htrace : WordTrace (prefixWord ++ tailWord_1372842) baseStart_1372842 baseEnd_1372842 := by
    simpa [prefixWord, tailWord_1372842, baseEnd_1372842] using wordTrace_append hprefix tailTrace_1372842
  have hstable : (prefixWord ++ tailWord_1372842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372842).length < 2 ^ (prefixWord ++ tailWord_1372842).sum := by decide
  have hdescent : baseEnd_1372842 < baseStart_1372842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372861 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1372861 : Nat := 118140960795 + 1372861 * 2 ^ 59
def prefixEnd_1372861 : Nat := 4983230072969 + 3 ^ 40 * 1372861 * 2
def baseEnd_1372861 : Nat := 704937564812258408723833

theorem tailTrace_1372861 : CollatzResearch.WordTrace tailWord_1372861 prefixEnd_1372861 704937564812258408723833 := by
  unfold tailWord_1372861
  simp only [CollatzResearch.WordTrace]
  refine ⟨50072354279366537837118437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33381569519577691891412291 50072354279366537837118437)
  ·
    refine ⟨9388566427381225844459707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50072354279366537837118437 9388566427381225844459707)
    ·
      refine ⟨14082849641071838766689561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9388566427381225844459707 14082849641071838766689561)
      ·
        refine ⟨10562137230803879075017171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14082849641071838766689561 10562137230803879075017171)
        ·
          refine ⟨15843205846205818612525757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10562137230803879075017171 15843205846205818612525757)
          ·
            refine ⟨5941202192327181979697159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15843205846205818612525757 5941202192327181979697159)
            ·
              refine ⟨8911803288490772969545739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941202192327181979697159 8911803288490772969545739)
              ·
                refine ⟨13367704932736159454318609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8911803288490772969545739 13367704932736159454318609)
                ·
                  refine ⟨10025778699552119590738957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13367704932736159454318609 10025778699552119590738957)
                  ·
                    refine ⟨3759667012332044846527109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10025778699552119590738957 3759667012332044846527109)
                    ·
                      refine ⟨704937564812258408723833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3759667012332044846527109 704937564812258408723833)
                      ·
                        rfl

theorem cell23_1372861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1372861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372861 prefixEnd_1372861 := by exact prefixLift 1372861
  have htrace : WordTrace (prefixWord ++ tailWord_1372861) baseStart_1372861 baseEnd_1372861 := by
    simpa [prefixWord, tailWord_1372861, baseEnd_1372861] using wordTrace_append hprefix tailTrace_1372861
  have hstable : (prefixWord ++ tailWord_1372861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372861).length < 2 ^ (prefixWord ++ tailWord_1372861).sum := by decide
  have hdescent : baseEnd_1372861 < baseStart_1372861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372881 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_1372881 : Nat := 118140960795 + 1372881 * 2 ^ 59
def prefixEnd_1372881 : Nat := 4983230072969 + 3 ^ 40 * 1372881 * 2
def baseEnd_1372881 : Nat := 704947834425348330473741

theorem tailTrace_1372881 : CollatzResearch.WordTrace tailWord_1372881 prefixEnd_1372881 704947834425348330473741 := by
  unfold tailWord_1372881
  simp only [CollatzResearch.WordTrace]
  refine ⟨50073083739294081252846497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33382055826196054168564331 50073083739294081252846497)
  ·
    refine ⟨37554812804470560939634873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50073083739294081252846497 37554812804470560939634873)
    ·
      refine ⟨28166109603352920704726155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37554812804470560939634873 28166109603352920704726155)
      ·
        refine ⟨42249164405029381057089233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28166109603352920704726155 42249164405029381057089233)
        ·
          refine ⟨31686873303772035792816925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42249164405029381057089233 31686873303772035792816925)
          ·
            refine ⟨11882577488914513422306347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31686873303772035792816925 11882577488914513422306347)
            ·
              refine ⟨17823866233371770133459521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11882577488914513422306347 17823866233371770133459521)
              ·
                refine ⟨13367899675028827600094641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17823866233371770133459521 13367899675028827600094641)
                ·
                  refine ⟨10025924756271620700070981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13367899675028827600094641 10025924756271620700070981)
                  ·
                    refine ⟨1879860891800928881263309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10025924756271620700070981 1879860891800928881263309)
                    ·
                      refine ⟨704947834425348330473741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1879860891800928881263309 704947834425348330473741)
                      ·
                        rfl

theorem cell23_1372881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_1372881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372881 prefixEnd_1372881 := by exact prefixLift 1372881
  have htrace : WordTrace (prefixWord ++ tailWord_1372881) baseStart_1372881 baseEnd_1372881 := by
    simpa [prefixWord, tailWord_1372881, baseEnd_1372881] using wordTrace_append hprefix tailTrace_1372881
  have hstable : (prefixWord ++ tailWord_1372881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372881).length < 2 ^ (prefixWord ++ tailWord_1372881).sum := by decide
  have hdescent : baseEnd_1372881 < baseStart_1372881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372899 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 1, 3, 2]
def baseStart_1372899 : Nat := 118140960795 + 1372899 * 2 ^ 59
def prefixEnd_1372899 : Nat := 4983230072969 + 3 ^ 40 * 1372899 * 2
def baseEnd_1372899 : Nat := 704957077077129260048659

theorem tailTrace_1372899 : CollatzResearch.WordTrace tailWord_1372899 prefixEnd_1372899 704957077077129260048659 := by
  unfold tailWord_1372899
  simp only [CollatzResearch.WordTrace]
  refine ⟨50073740253228870327001751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33382493502152580218001167 50073740253228870327001751)
  ·
    refine ⟨75110610379843305490502627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50073740253228870327001751 75110610379843305490502627)
    ·
      refine ⟨112665915569764958235753941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75110610379843305490502627 112665915569764958235753941)
      ·
        refine ⟨2640607396166366208650483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 112665915569764958235753941 2640607396166366208650483)
        ·
          refine ⟨3960911094249549312975725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640607396166366208650483 3960911094249549312975725)
          ·
            refine ⟨1485341660343580992365897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3960911094249549312975725 1485341660343580992365897)
            ·
              refine ⟨1114006245257685744274423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485341660343580992365897 1114006245257685744274423)
              ·
                refine ⟨1671009367886528616411635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114006245257685744274423 1671009367886528616411635)
                ·
                  refine ⟨2506514051829792924617453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671009367886528616411635 2506514051829792924617453)
                  ·
                    refine ⟨939942769436172346731545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2506514051829792924617453 939942769436172346731545)
                    ·
                      refine ⟨704957077077129260048659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939942769436172346731545 704957077077129260048659)
                      ·
                        rfl

theorem cell23_1372899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_1372899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372899 prefixEnd_1372899 := by exact prefixLift 1372899
  have htrace : WordTrace (prefixWord ++ tailWord_1372899) baseStart_1372899 baseEnd_1372899 := by
    simpa [prefixWord, tailWord_1372899, baseEnd_1372899] using wordTrace_append hprefix tailTrace_1372899
  have hstable : (prefixWord ++ tailWord_1372899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372899).length < 2 ^ (prefixWord ++ tailWord_1372899).sum := by decide
  have hdescent : baseEnd_1372899 < baseStart_1372899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372918 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_1372918 : Nat := 118140960795 + 1372918 * 2 ^ 59
def prefixEnd_1372918 : Nat := 4983230072969 + 3 ^ 40 * 1372918 * 2
def baseEnd_1372918 : Nat := 78329648134396076190119

theorem tailTrace_1372918 : CollatzResearch.WordTrace tailWord_1372918 prefixEnd_1372918 78329648134396076190119 := by
  unfold tailWord_1372918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129652077510002285746463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33382955493440024381295605 3129652077510002285746463)
  ·
    refine ⟨4694478116265003428619695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3129652077510002285746463 4694478116265003428619695)
    ·
      refine ⟨7041717174397505142929543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4694478116265003428619695 7041717174397505142929543)
      ·
        refine ⟨10562575761596257714394315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041717174397505142929543 10562575761596257714394315)
        ·
          refine ⟨15843863642394386571591473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10562575761596257714394315 15843863642394386571591473)
          ·
            refine ⟨11882897731795789928693605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15843863642394386571591473 11882897731795789928693605)
            ·
              refine ⟨2228043324711710611630051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11882897731795789928693605 2228043324711710611630051)
              ·
                refine ⟨3342064987067565917445077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228043324711710611630051 3342064987067565917445077)
                ·
                  refine ⟨78329648134396076190119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3342064987067565917445077 78329648134396076190119)
                  ·
                    rfl

theorem cell23_1372918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_1372918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372918 prefixEnd_1372918 := by exact prefixLift 1372918
  have htrace : WordTrace (prefixWord ++ tailWord_1372918) baseStart_1372918 baseEnd_1372918 := by
    simpa [prefixWord, tailWord_1372918, baseEnd_1372918] using wordTrace_append hprefix tailTrace_1372918
  have hstable : (prefixWord ++ tailWord_1372918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372918).length < 2 ^ (prefixWord ++ tailWord_1372918).sum := by decide
  have hdescent : baseEnd_1372918 < baseStart_1372918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372988 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_1372988 : Nat := 118140960795 + 1372988 * 2 ^ 59
def prefixEnd_1372988 : Nat := 4983230072969 + 3 ^ 40 * 1372988 * 2
def baseEnd_1372988 : Nat := 705002776855379411835749

theorem tailTrace_1372988 : CollatzResearch.WordTrace tailWord_1372988 prefixEnd_1372988 705002776855379411835749 := by
  unfold tailWord_1372988
  simp only [CollatzResearch.WordTrace]
  refine ⟨25038493174953219263495809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33384657566604292351327745 25038493174953219263495809)
  ·
    refine ⟨18778869881214914447621857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25038493174953219263495809 18778869881214914447621857)
    ·
      refine ⟨14084152410911185835716393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18778869881214914447621857 14084152410911185835716393)
      ·
        refine ⟨10563114308183389376787295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14084152410911185835716393 10563114308183389376787295)
        ·
          refine ⟨15844671462275084065180943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10563114308183389376787295 15844671462275084065180943)
          ·
            refine ⟨23767007193412626097771415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15844671462275084065180943 23767007193412626097771415)
            ·
              refine ⟨35650510790118939146657123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23767007193412626097771415 35650510790118939146657123)
              ·
                refine ⟨53475766185178408719985685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35650510790118939146657123 53475766185178408719985685)
                ·
                  refine ⟨2506676539930237908749329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53475766185178408719985685 2506676539930237908749329)
                  ·
                    refine ⟨1880007404947678431561997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2506676539930237908749329 1880007404947678431561997)
                    ·
                      refine ⟨705002776855379411835749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1880007404947678431561997 705002776855379411835749)
                      ·
                        rfl

theorem cell23_1372988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_1372988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1372988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1372988 prefixEnd_1372988 := by exact prefixLift 1372988
  have htrace : WordTrace (prefixWord ++ tailWord_1372988) baseStart_1372988 baseEnd_1372988 := by
    simpa [prefixWord, tailWord_1372988, baseEnd_1372988] using wordTrace_append hprefix tailTrace_1372988
  have hstable : (prefixWord ++ tailWord_1372988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372988).length < 2 ^ (prefixWord ++ tailWord_1372988).sum := by decide
  have hdescent : baseEnd_1372988 < baseStart_1372988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373068 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_1373068 : Nat := 118140960795 + 1373068 * 2 ^ 59
def prefixEnd_1373068 : Nat := 4983230072969 + 3 ^ 40 * 1373068 * 2
def baseEnd_1373068 : Nat := 235014618435913032945127

theorem tailTrace_1373068 : CollatzResearch.WordTrace tailWord_1373068 prefixEnd_1373068 235014618435913032945127 := by
  unfold tailWord_1373068
  simp only [CollatzResearch.WordTrace]
  refine ⟨25039952094808306094951929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33386602793077741459935905 25039952094808306094951929)
  ·
    refine ⟨18779964071106229571213947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25039952094808306094951929 18779964071106229571213947)
    ·
      refine ⟨28169946106659344356820921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18779964071106229571213947 28169946106659344356820921)
      ·
        refine ⟨21127459579994508267615691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28169946106659344356820921 21127459579994508267615691)
        ·
          refine ⟨31691189369991762401423537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21127459579994508267615691 31691189369991762401423537)
          ·
            refine ⟨23768392027493821801067653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31691189369991762401423537 23768392027493821801067653)
            ·
              refine ⟨4456573505155091587700185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23768392027493821801067653 4456573505155091587700185)
              ·
                refine ⟨3342430128866318690775139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4456573505155091587700185 3342430128866318690775139)
                ·
                  refine ⟨5013645193299478036162709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342430128866318690775139 5013645193299478036162709)
                  ·
                    refine ⟨235014618435913032945127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5013645193299478036162709 235014618435913032945127)
                    ·
                      rfl

theorem cell23_1373068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_1373068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373068 prefixEnd_1373068 := by exact prefixLift 1373068
  have htrace : WordTrace (prefixWord ++ tailWord_1373068) baseStart_1373068 baseEnd_1373068 := by
    simpa [prefixWord, tailWord_1373068, baseEnd_1373068] using wordTrace_append hprefix tailTrace_1373068
  have hstable : (prefixWord ++ tailWord_1373068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373068).length < 2 ^ (prefixWord ++ tailWord_1373068).sum := by decide
  have hdescent : baseEnd_1373068 < baseStart_1373068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373085 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1373085 : Nat := 118140960795 + 1373085 * 2 ^ 59
def prefixEnd_1373085 : Nat := 4983230072969 + 3 ^ 40 * 1373085 * 2
def baseEnd_1373085 : Nat := 235017528159621844107601

theorem tailTrace_1373085 : CollatzResearch.WordTrace tailWord_1373085 prefixEnd_1373085 235017528159621844107601 := by
  unfold tailWord_1373085
  simp only [CollatzResearch.WordTrace]
  refine ⟨50080524230555024093272709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33387016153703349395515139 50080524230555024093272709)
  ·
    refine ⟨9390098293229067017488633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50080524230555024093272709 9390098293229067017488633)
    ·
      refine ⟨7042573719921800263116475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9390098293229067017488633 7042573719921800263116475)
      ·
        refine ⟨10563860579882700394674713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7042573719921800263116475 10563860579882700394674713)
        ·
          refine ⟨7922895434912025296006035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10563860579882700394674713 7922895434912025296006035)
          ·
            refine ⟨11884343152368037944009053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7922895434912025296006035 11884343152368037944009053)
            ·
              refine ⟨4456628682138014229003395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11884343152368037944009053 4456628682138014229003395)
              ·
                refine ⟨6684943023207021343505093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456628682138014229003395 6684943023207021343505093)
                ·
                  refine ⟨1253426816851316501907205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6684943023207021343505093 1253426816851316501907205)
                  ·
                    refine ⟨235017528159621844107601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1253426816851316501907205 235017528159621844107601)
                    ·
                      rfl

theorem cell23_1373085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1373085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373085 prefixEnd_1373085 := by exact prefixLift 1373085
  have htrace : WordTrace (prefixWord ++ tailWord_1373085) baseStart_1373085 baseEnd_1373085 := by
    simpa [prefixWord, tailWord_1373085, baseEnd_1373085] using wordTrace_append hprefix tailTrace_1373085
  have hstable : (prefixWord ++ tailWord_1373085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373085).length < 2 ^ (prefixWord ++ tailWord_1373085).sum := by decide
  have hdescent : baseEnd_1373085 < baseStart_1373085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373088 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1373088 : Nat := 118140960795 + 1373088 * 2 ^ 59
def prefixEnd_1373088 : Nat := 4983230072969 + 3 ^ 40 * 1373088 * 2
def baseEnd_1373088 : Nat := 705054124920829020585289

theorem tailTrace_1373088 : CollatzResearch.WordTrace tailWord_1373088 prefixEnd_1373088 705054124920829020585289 := by
  unfold tailWord_1373088
  simp only [CollatzResearch.WordTrace]
  refine ⟨25040316824772077802815959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33387089099696103737087945 25040316824772077802815959)
  ·
    refine ⟨37560475237158116704223939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25040316824772077802815959 37560475237158116704223939)
    ·
      refine ⟨56340712855737175056335909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37560475237158116704223939 56340712855737175056335909)
      ·
        refine ⟨10563883660450720323062983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56340712855737175056335909 10563883660450720323062983)
        ·
          refine ⟨15845825490676080484594475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10563883660450720323062983 15845825490676080484594475)
          ·
            refine ⟨23768738236014120726891713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15845825490676080484594475 23768738236014120726891713)
            ·
              refine ⟨17826553677010590545168785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23768738236014120726891713 17826553677010590545168785)
              ·
                refine ⟨13369915257757942908876589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17826553677010590545168785 13369915257757942908876589)
                ·
                  refine ⟨5013718221659228590828721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13369915257757942908876589 5013718221659228590828721)
                  ·
                    refine ⟨3760288666244421443121541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5013718221659228590828721 3760288666244421443121541)
                    ·
                      refine ⟨705054124920829020585289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3760288666244421443121541 705054124920829020585289)
                      ·
                        rfl

theorem cell23_1373088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1373088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373088 prefixEnd_1373088 := by exact prefixLift 1373088
  have htrace : WordTrace (prefixWord ++ tailWord_1373088) baseStart_1373088 baseEnd_1373088 := by
    simpa [prefixWord, tailWord_1373088, baseEnd_1373088] using wordTrace_append hprefix tailTrace_1373088
  have hstable : (prefixWord ++ tailWord_1373088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373088).length < 2 ^ (prefixWord ++ tailWord_1373088).sum := by decide
  have hdescent : baseEnd_1373088 < baseStart_1373088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373105 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1373105 : Nat := 118140960795 + 1373105 * 2 ^ 59
def prefixEnd_1373105 : Nat := 4983230072969 + 3 ^ 40 * 1373105 * 2
def baseEnd_1373105 : Nat := 705062854091955454072711

theorem tailTrace_1373105 : CollatzResearch.WordTrace tailWord_1373105 prefixEnd_1373105 705062854091955454072711 := by
  unfold tailWord_1373105
  simp only [CollatzResearch.WordTrace]
  refine ⟨50081253690482567509000769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33387502460321711672667179 50081253690482567509000769)
  ·
    refine ⟨37560940267861925631750577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50081253690482567509000769 37560940267861925631750577)
    ·
      refine ⟨28170705200896444223812933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37560940267861925631750577 28170705200896444223812933)
      ·
        refine ⟨5282007225168083291964925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28170705200896444223812933 5282007225168083291964925)
        ·
          refine ⟨1980752709438031234486847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5282007225168083291964925 1980752709438031234486847)
          ·
            refine ⟨2971129064157046851730271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980752709438031234486847 2971129064157046851730271)
            ·
              refine ⟨4456693596235570277595407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971129064157046851730271 4456693596235570277595407)
              ·
                refine ⟨6685040394353355416393111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456693596235570277595407 6685040394353355416393111)
                ·
                  refine ⟨10027560591530033124589667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6685040394353355416393111 10027560591530033124589667)
                  ·
                    refine ⟨15041340887295049686884501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10027560591530033124589667 15041340887295049686884501)
                    ·
                      refine ⟨705062854091955454072711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15041340887295049686884501 705062854091955454072711)
                      ·
                        rfl

theorem cell23_1373105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1373105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373105 prefixEnd_1373105 := by exact prefixLift 1373105
  have htrace : WordTrace (prefixWord ++ tailWord_1373105) baseStart_1373105 baseEnd_1373105 := by
    simpa [prefixWord, tailWord_1373105, baseEnd_1373105] using wordTrace_append hprefix tailTrace_1373105
  have hstable : (prefixWord ++ tailWord_1373105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373105).length < 2 ^ (prefixWord ++ tailWord_1373105).sum := by decide
  have hdescent : baseEnd_1373105 < baseStart_1373105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373112 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_1373112 : Nat := 118140960795 + 1373112 * 2 ^ 59
def prefixEnd_1373112 : Nat := 4983230072969 + 3 ^ 40 * 1373112 * 2
def baseEnd_1373112 : Nat := 705066448456536926685179

theorem tailTrace_1373112 : CollatzResearch.WordTrace tailWord_1373112 prefixEnd_1373112 705066448456536926685179 := by
  unfold tailWord_1373112
  simp only [CollatzResearch.WordTrace]
  refine ⟨25040754500728603852252795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33387672667638138469670393 25040754500728603852252795)
  ·
    refine ⟨37561131751092905778379193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25040754500728603852252795 37561131751092905778379193)
    ·
      refine ⟨28170848813319679333784395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37561131751092905778379193 28170848813319679333784395)
      ·
        refine ⟨42256273219979519000676593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28170848813319679333784395 42256273219979519000676593)
        ·
          refine ⟨31692204914984639250507445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42256273219979519000676593 31692204914984639250507445)
          ·
            refine ⟨2971144210779809929735073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31692204914984639250507445 2971144210779809929735073)
            ·
              refine ⟨2228358158084857447301305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2971144210779809929735073 2228358158084857447301305)
              ·
                refine ⟨1671268618563643085475979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228358158084857447301305 1671268618563643085475979)
                ·
                  refine ⟨2506902927845464628213969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671268618563643085475979 2506902927845464628213969)
                  ·
                    refine ⟨1880177195884098471160477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2506902927845464628213969 1880177195884098471160477)
                    ·
                      refine ⟨705066448456536926685179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1880177195884098471160477 705066448456536926685179)
                      ·
                        rfl

theorem cell23_1373112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_1373112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373112 prefixEnd_1373112 := by exact prefixLift 1373112
  have htrace : WordTrace (prefixWord ++ tailWord_1373112) baseStart_1373112 baseEnd_1373112 := by
    simpa [prefixWord, tailWord_1373112, baseEnd_1373112] using wordTrace_append hprefix tailTrace_1373112
  have hstable : (prefixWord ++ tailWord_1373112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373112).length < 2 ^ (prefixWord ++ tailWord_1373112).sum := by decide
  have hdescent : baseEnd_1373112 < baseStart_1373112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373159 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1373159 : Nat := 118140960795 + 1373159 * 2 ^ 59
def prefixEnd_1373159 : Nat := 4983230072969 + 3 ^ 40 * 1373159 * 2
def baseEnd_1373159 : Nat := 705090582047298242797463

theorem tailTrace_1373159 : CollatzResearch.WordTrace tailWord_1373159 prefixEnd_1373159 705090582047298242797463 := by
  unfold tailWord_1373159
  simp only [CollatzResearch.WordTrace]
  refine ⟨50083223232286934731466531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33388815488191289820977687 50083223232286934731466531)
  ·
    refine ⟨75124834848430402097199797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50083223232286934731466531 75124834848430402097199797)
    ·
      refine ⟨7042953267040350196612481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75124834848430402097199797 7042953267040350196612481)
      ·
        refine ⟨5282214950280262647459361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7042953267040350196612481 5282214950280262647459361)
        ·
          refine ⟨3961661212710196985594521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5282214950280262647459361 3961661212710196985594521)
          ·
            refine ⟨2971245909532647739195891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3961661212710196985594521 2971245909532647739195891)
            ·
              refine ⟨4456868864298971608793837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971245909532647739195891 4456868864298971608793837)
              ·
                refine ⟨1671325824112114353297689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4456868864298971608793837 1671325824112114353297689)
                ·
                  refine ⟨1253494368084085764973267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1671325824112114353297689 1253494368084085764973267)
                  ·
                    refine ⟨1880241552126128647459901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1253494368084085764973267 1880241552126128647459901)
                    ·
                      refine ⟨705090582047298242797463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1880241552126128647459901 705090582047298242797463)
                      ·
                        rfl

theorem cell23_1373159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1373159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373159 prefixEnd_1373159 := by exact prefixLift 1373159
  have htrace : WordTrace (prefixWord ++ tailWord_1373159) baseStart_1373159 baseEnd_1373159 := by
    simpa [prefixWord, tailWord_1373159, baseEnd_1373159] using wordTrace_append hprefix tailTrace_1373159
  have hstable : (prefixWord ++ tailWord_1373159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373159).length < 2 ^ (prefixWord ++ tailWord_1373159).sum := by decide
  have hdescent : baseEnd_1373159 < baseStart_1373159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373169 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 1, 3, 2]
def baseStart_1373169 : Nat := 118140960795 + 1373169 * 2 ^ 59
def prefixEnd_1373169 : Nat := 4983230072969 + 3 ^ 40 * 1373169 * 2
def baseEnd_1373169 : Nat := 705095716853843203672417

theorem tailTrace_1373169 : CollatzResearch.WordTrace tailWord_1373169 prefixEnd_1373169 705095716853843203672417 := by
  unfold tailWord_1373169
  simp only [CollatzResearch.WordTrace]
  refine ⟨50083587962250706439330561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33389058641500470959553707 50083587962250706439330561)
  ·
    refine ⟨37562690971688029829497921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50083587962250706439330561 37562690971688029829497921)
    ·
      refine ⟨28172018228766022372123441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37562690971688029829497921 28172018228766022372123441)
      ·
        refine ⟨21129013671574516779092581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28172018228766022372123441 21129013671574516779092581)
        ·
          refine ⟨3961690063420221896079859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21129013671574516779092581 3961690063420221896079859)
          ·
            refine ⟨5942535095130332844119789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961690063420221896079859 5942535095130332844119789)
            ·
              refine ⟨2228450660673874816544921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5942535095130332844119789 2228450660673874816544921)
              ·
                refine ⟨1671337995505406112408691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228450660673874816544921 1671337995505406112408691)
                ·
                  refine ⟨2507006993258109168613037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671337995505406112408691 2507006993258109168613037)
                  ·
                    refine ⟨940127622471790938229889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507006993258109168613037 940127622471790938229889)
                    ·
                      refine ⟨705095716853843203672417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940127622471790938229889 705095716853843203672417)
                      ·
                        rfl

theorem cell23_1373169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_1373169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373169 prefixEnd_1373169 := by exact prefixLift 1373169
  have htrace : WordTrace (prefixWord ++ tailWord_1373169) baseStart_1373169 baseEnd_1373169 := by
    simpa [prefixWord, tailWord_1373169, baseEnd_1373169] using wordTrace_append hprefix tailTrace_1373169
  have hstable : (prefixWord ++ tailWord_1373169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373169).length < 2 ^ (prefixWord ++ tailWord_1373169).sum := by decide
  have hdescent : baseEnd_1373169 < baseStart_1373169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373185 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1373185 : Nat := 118140960795 + 1373185 * 2 ^ 59
def prefixEnd_1373185 : Nat := 4983230072969 + 3 ^ 40 * 1373185 * 2
def baseEnd_1373185 : Nat := 705103932544315141072343

theorem tailTrace_1373185 : CollatzResearch.WordTrace tailWord_1373185 prefixEnd_1373185 705103932544315141072343 := by
  unfold tailWord_1373185
  simp only [CollatzResearch.WordTrace]
  refine ⟨50084171530192741171913009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33389447686795160781275339 50084171530192741171913009)
  ·
    refine ⟨37563128647644555878934757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50084171530192741171913009 37563128647644555878934757)
    ·
      refine ⟨7043086621433354227300267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37563128647644555878934757 7043086621433354227300267)
      ·
        refine ⟨10564629932150031340950401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7043086621433354227300267 10564629932150031340950401)
        ·
          refine ⟨7923472449112523505712801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10564629932150031340950401 7923472449112523505712801)
          ·
            refine ⟨5942604336834392629284601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7923472449112523505712801 5942604336834392629284601)
            ·
              refine ⟨4456953252625794471963451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5942604336834392629284601 4456953252625794471963451)
              ·
                refine ⟨6685429878938691707945177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456953252625794471963451 6685429878938691707945177)
                ·
                  refine ⟨5014072409204018780958883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6685429878938691707945177 5014072409204018780958883)
                  ·
                    refine ⟨7521108613806028171438325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5014072409204018780958883 7521108613806028171438325)
                    ·
                      refine ⟨705103932544315141072343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7521108613806028171438325 705103932544315141072343)
                      ·
                        rfl

theorem cell23_1373185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1373185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373185 prefixEnd_1373185 := by exact prefixLift 1373185
  have htrace : WordTrace (prefixWord ++ tailWord_1373185) baseStart_1373185 baseEnd_1373185 := by
    simpa [prefixWord, tailWord_1373185, baseEnd_1373185] using wordTrace_append hprefix tailTrace_1373185
  have hstable : (prefixWord ++ tailWord_1373185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373185).length < 2 ^ (prefixWord ++ tailWord_1373185).sum := by decide
  have hdescent : baseEnd_1373185 < baseStart_1373185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373212 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1373212 : Nat := 118140960795 + 1373212 * 2 ^ 59
def prefixEnd_1373212 : Nat := 4983230072969 + 3 ^ 40 * 1373212 * 2
def baseEnd_1373212 : Nat := 705117796521986535434719

theorem tailTrace_1373212 : CollatzResearch.WordTrace tailWord_1373212 prefixEnd_1373212 705117796521986535434719 := by
  unfold tailWord_1373212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25042578150547462391572945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33390104200729949855430593 25042578150547462391572945)
  ·
    refine ⟨18781933612910596793679709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25042578150547462391572945 18781933612910596793679709)
    ·
      refine ⟨7043225104841473797629891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18781933612910596793679709 7043225104841473797629891)
      ·
        refine ⟨10564837657262210696444837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7043225104841473797629891 10564837657262210696444837)
        ·
          refine ⟨1980907060736664505583407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10564837657262210696444837 1980907060736664505583407)
          ·
            refine ⟨2971360591104996758375111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980907060736664505583407 2971360591104996758375111)
            ·
              refine ⟨4457040886657495137562667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971360591104996758375111 4457040886657495137562667)
              ·
                refine ⟨6685561329986242706344001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457040886657495137562667 6685561329986242706344001)
                ·
                  refine ⟨5014170997489682029758001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6685561329986242706344001 5014170997489682029758001)
                  ·
                    refine ⟨3760628248117261522318501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5014170997489682029758001 3760628248117261522318501)
                    ·
                      refine ⟨705117796521986535434719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3760628248117261522318501 705117796521986535434719)
                      ·
                        rfl

theorem cell23_1373212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1373212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373212 prefixEnd_1373212 := by exact prefixLift 1373212
  have htrace : WordTrace (prefixWord ++ tailWord_1373212) baseStart_1373212 baseEnd_1373212 := by
    simpa [prefixWord, tailWord_1373212, baseEnd_1373212] using wordTrace_append hprefix tailTrace_1373212
  have hstable : (prefixWord ++ tailWord_1373212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373212).length < 2 ^ (prefixWord ++ tailWord_1373212).sum := by decide
  have hdescent : baseEnd_1373212 < baseStart_1373212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373215 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 3]
def baseStart_1373215 : Nat := 118140960795 + 1373215 * 2 ^ 59
def prefixEnd_1373215 : Nat := 4983230072969 + 3 ^ 40 * 1373215 * 2
def baseEnd_1373215 : Nat := 705119336963950023697205

theorem tailTrace_1373215 : CollatzResearch.WordTrace tailWord_1373215 prefixEnd_1373215 705119336963950023697205 := by
  unfold tailWord_1373215
  simp only [CollatzResearch.WordTrace]
  refine ⟨50085265720084056295505099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33390177146722704197003399 50085265720084056295505099)
  ·
    refine ⟨75127898580126084443257649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50085265720084056295505099 75127898580126084443257649)
    ·
      refine ⟨56345923935094563332443237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75127898580126084443257649 56345923935094563332443237)
      ·
        refine ⟨10564860737830230624833107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56345923935094563332443237 10564860737830230624833107)
        ·
          refine ⟨15847291106745345937249661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10564860737830230624833107 15847291106745345937249661)
          ·
            refine ⟨5942734165029504726468623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15847291106745345937249661 5942734165029504726468623)
            ·
              refine ⟨8914101247544257089702935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5942734165029504726468623 8914101247544257089702935)
              ·
                refine ⟨13371151871316385634554403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8914101247544257089702935 13371151871316385634554403)
                ·
                  refine ⟨20056727806974578451831605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13371151871316385634554403 20056727806974578451831605)
                  ·
                    refine ⟨1880318231903866729859213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20056727806974578451831605 1880318231903866729859213)
                    ·
                      refine ⟨705119336963950023697205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1880318231903866729859213 705119336963950023697205)
                      ·
                        rfl

theorem cell23_1373215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_1373215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373215 prefixEnd_1373215 := by exact prefixLift 1373215
  have htrace : WordTrace (prefixWord ++ tailWord_1373215) baseStart_1373215 baseEnd_1373215 := by
    simpa [prefixWord, tailWord_1373215, baseEnd_1373215] using wordTrace_append hprefix tailTrace_1373215
  have hstable : (prefixWord ++ tailWord_1373215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373215).length < 2 ^ (prefixWord ++ tailWord_1373215).sum := by decide
  have hdescent : baseEnd_1373215 < baseStart_1373215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373216 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1373216 : Nat := 118140960795 + 1373216 * 2 ^ 59
def prefixEnd_1373216 : Nat := 4983230072969 + 3 ^ 40 * 1373216 * 2
def baseEnd_1373216 : Nat := 705119850444604519784701

theorem tailTrace_1373216 : CollatzResearch.WordTrace tailWord_1373216 prefixEnd_1373216 705119850444604519784701 := by
  unfold tailWord_1373216
  simp only [CollatzResearch.WordTrace]
  refine ⟨25042651096540216733145751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33390201462053622310861001 25042651096540216733145751)
  ·
    refine ⟨37563976644810325099718627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25042651096540216733145751 37563976644810325099718627)
    ·
      refine ⟨56345964967215487649577941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37563976644810325099718627 56345964967215487649577941)
      ·
        refine ⟨1320608553919112991786983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 56345964967215487649577941 1320608553919112991786983)
        ·
          refine ⟨1980912830878669487680475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320608553919112991786983 1980912830878669487680475)
          ·
            refine ⟨2971369246318004231520713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980912830878669487680475 2971369246318004231520713)
            ·
              refine ⟨2228526934738503173640535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2971369246318004231520713 2228526934738503173640535)
              ·
                refine ⟨3342790402107754760460803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228526934738503173640535 3342790402107754760460803)
                ·
                  refine ⟨5014185603161632140691205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342790402107754760460803 5014185603161632140691205)
                  ·
                    refine ⟨940159800592806026379601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014185603161632140691205 940159800592806026379601)
                    ·
                      refine ⟨705119850444604519784701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940159800592806026379601 705119850444604519784701)
                      ·
                        rfl

theorem cell23_1373216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1373216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373216 prefixEnd_1373216 := by exact prefixLift 1373216
  have htrace : WordTrace (prefixWord ++ tailWord_1373216) baseStart_1373216 baseEnd_1373216 := by
    simpa [prefixWord, tailWord_1373216, baseEnd_1373216] using wordTrace_append hprefix tailTrace_1373216
  have hstable : (prefixWord ++ tailWord_1373216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373216).length < 2 ^ (prefixWord ++ tailWord_1373216).sum := by decide
  have hdescent : baseEnd_1373216 < baseStart_1373216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373272 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 2, 4, 2]
def baseStart_1373272 : Nat := 118140960795 + 1373272 * 2 ^ 59
def prefixEnd_1373272 : Nat := 4983230072969 + 3 ^ 40 * 1373272 * 2
def baseEnd_1373272 : Nat := 705148605361256300684443

theorem tailTrace_1373272 : CollatzResearch.WordTrace tailWord_1373272 prefixEnd_1373272 705148605361256300684443 := by
  unfold tailWord_1373272
  simp only [CollatzResearch.WordTrace]
  refine ⟨25043672340438777515165035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33391563120585036686886713 25043672340438777515165035)
  ·
    refine ⟨37565508510658166272747553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25043672340438777515165035 37565508510658166272747553)
    ·
      refine ⟨28174131382993624704560665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37565508510658166272747553 28174131382993624704560665)
      ·
        refine ⟨21130598537245218528420499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28174131382993624704560665 21130598537245218528420499)
        ·
          refine ⟨31695897805867827792630749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21130598537245218528420499 31695897805867827792630749)
          ·
            refine ⟨11885961677200435422236531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31695897805867827792630749 11885961677200435422236531)
            ·
              refine ⟨17828942515800653133354797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11885961677200435422236531 17828942515800653133354797)
              ·
                refine ⟨6685853443425244925008049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17828942515800653133354797 6685853443425244925008049)
                ·
                  refine ⟨5014390082568933693756037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6685853443425244925008049 5014390082568933693756037)
                  ·
                    refine ⟨940198140481675067579257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014390082568933693756037 940198140481675067579257)
                    ·
                      refine ⟨705148605361256300684443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940198140481675067579257 705148605361256300684443)
                      ·
                        rfl

theorem cell23_1373272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_1373272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373272 prefixEnd_1373272 := by exact prefixLift 1373272
  have htrace : WordTrace (prefixWord ++ tailWord_1373272) baseStart_1373272 baseEnd_1373272 := by
    simpa [prefixWord, tailWord_1373272, baseEnd_1373272] using wordTrace_append hprefix tailTrace_1373272
  have hstable : (prefixWord ++ tailWord_1373272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373272).length < 2 ^ (prefixWord ++ tailWord_1373272).sum := by decide
  have hdescent : baseEnd_1373272 < baseStart_1373272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373285 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1373285 : Nat := 118140960795 + 1373285 * 2 ^ 59
def prefixEnd_1373285 : Nat := 4983230072969 + 3 ^ 40 * 1373285 * 2
def baseEnd_1373285 : Nat := 705155280609764749821883

theorem tailTrace_1373285 : CollatzResearch.WordTrace tailWord_1373285 prefixEnd_1373285 705155280609764749821883 := by
  unfold tailWord_1373285
  simp only [CollatzResearch.WordTrace]
  refine ⟨50087818829830458250553309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33391879219886972167035539 50087818829830458250553309)
  ·
    refine ⟨18782932061186421843957491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50087818829830458250553309 18782932061186421843957491)
    ·
      refine ⟨28174398091779632765936237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18782932061186421843957491 28174398091779632765936237)
      ·
        refine ⟨10565399284417362287226089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28174398091779632765936237 10565399284417362287226089)
        ·
          refine ⟨7924049463313021715419567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10565399284417362287226089 7924049463313021715419567)
          ·
            refine ⟨11886074194969532573129351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7924049463313021715419567 11886074194969532573129351)
            ·
              refine ⟨17829111292454298859694027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11886074194969532573129351 17829111292454298859694027)
              ·
                refine ⟨26743666938681448289541041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17829111292454298859694027 26743666938681448289541041)
                ·
                  refine ⟨20057750204011086217155781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26743666938681448289541041 20057750204011086217155781)
                  ·
                    refine ⟨3760828163252078665716709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20057750204011086217155781 3760828163252078665716709)
                    ·
                      refine ⟨705155280609764749821883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3760828163252078665716709 705155280609764749821883)
                      ·
                        rfl

theorem cell23_1373285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1373285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373285 prefixEnd_1373285 := by exact prefixLift 1373285
  have htrace : WordTrace (prefixWord ++ tailWord_1373285) baseStart_1373285 baseEnd_1373285 := by
    simpa [prefixWord, tailWord_1373285, baseEnd_1373285] using wordTrace_append hprefix tailTrace_1373285
  have hstable : (prefixWord ++ tailWord_1373285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373285).length < 2 ^ (prefixWord ++ tailWord_1373285).sum := by decide
  have hdescent : baseEnd_1373285 < baseStart_1373285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373292 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_1373292 : Nat := 118140960795 + 1373292 * 2 ^ 59
def prefixEnd_1373292 : Nat := 4983230072969 + 3 ^ 40 * 1373292 * 2
def baseEnd_1373292 : Nat := 705158874974346222434351

theorem tailTrace_1373292 : CollatzResearch.WordTrace tailWord_1373292 prefixEnd_1373292 705158874974346222434351 := by
  unfold tailWord_1373292
  simp only [CollatzResearch.WordTrace]
  refine ⟨25044037070402549223029065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33392049427203398964038753 25044037070402549223029065)
  ·
    refine ⟨18783027802801911917271799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25044037070402549223029065 18783027802801911917271799)
    ·
      refine ⟨28174541704202867875907699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18783027802801911917271799 28174541704202867875907699)
      ·
        refine ⟨42261812556304301813861549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28174541704202867875907699 42261812556304301813861549)
        ·
          refine ⟨15848179708614113180198081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42261812556304301813861549 15848179708614113180198081)
          ·
            refine ⟨11886134781460584885148561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15848179708614113180198081 11886134781460584885148561)
            ·
              refine ⟨8914601086095438663861421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11886134781460584885148561 8914601086095438663861421)
              ·
                refine ⟨3342975407285789498948033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8914601086095438663861421 3342975407285789498948033)
                ·
                  refine ⟨2507231555464342124211025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3342975407285789498948033 2507231555464342124211025)
                  ·
                    refine ⟨1880423666598256593158269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2507231555464342124211025 1880423666598256593158269)
                    ·
                      refine ⟨705158874974346222434351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1880423666598256593158269 705158874974346222434351)
                      ·
                        rfl

theorem cell23_1373292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_1373292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373292 prefixEnd_1373292 := by exact prefixLift 1373292
  have htrace : WordTrace (prefixWord ++ tailWord_1373292) baseStart_1373292 baseEnd_1373292 := by
    simpa [prefixWord, tailWord_1373292, baseEnd_1373292] using wordTrace_append hprefix tailTrace_1373292
  have hstable : (prefixWord ++ tailWord_1373292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373292).length < 2 ^ (prefixWord ++ tailWord_1373292).sum := by decide
  have hdescent : baseEnd_1373292 < baseStart_1373292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373349 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 2, 3, 2]
def baseStart_1373349 : Nat := 118140960795 + 1373349 * 2 ^ 59
def prefixEnd_1373349 : Nat := 4983230072969 + 3 ^ 40 * 1373349 * 2
def baseEnd_1373349 : Nat := 705188143371652499421589

theorem tailTrace_1373349 : CollatzResearch.WordTrace tailWord_1373349 prefixEnd_1373349 705188143371652499421589 := by
  unfold tailWord_1373349
  simp only [CollatzResearch.WordTrace]
  refine ⟨50090153101598597180883101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33393435401065731453922067 50090153101598597180883101)
  ·
    refine ⟨18783807413099473942831163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50090153101598597180883101 18783807413099473942831163)
    ·
      refine ⟨28175711119649210914246745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18783807413099473942831163 28175711119649210914246745)
      ·
        refine ⟨21131783339736908185685059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28175711119649210914246745 21131783339736908185685059)
        ·
          refine ⟨31697675009605362278527589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21131783339736908185685059 31697675009605362278527589)
          ·
            refine ⟨5943314064301005427223923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31697675009605362278527589 5943314064301005427223923)
            ·
              refine ⟨8914971096451508140835885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943314064301005427223923 8914971096451508140835885)
              ·
                refine ⟨3343114161169315552813457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8914971096451508140835885 3343114161169315552813457)
                ·
                  refine ⟨2507335620876986664610093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343114161169315552813457 2507335620876986664610093)
                  ·
                    refine ⟨940250857828869999228785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507335620876986664610093 940250857828869999228785)
                    ·
                      refine ⟨705188143371652499421589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940250857828869999228785 705188143371652499421589)
                      ·
                        rfl

theorem cell23_1373349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_1373349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373349 prefixEnd_1373349 := by exact prefixLift 1373349
  have htrace : WordTrace (prefixWord ++ tailWord_1373349) baseStart_1373349 baseEnd_1373349 := by
    simpa [prefixWord, tailWord_1373349, baseEnd_1373349] using wordTrace_append hprefix tailTrace_1373349
  have hstable : (prefixWord ++ tailWord_1373349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373349).length < 2 ^ (prefixWord ++ tailWord_1373349).sum := by decide
  have hdescent : baseEnd_1373349 < baseStart_1373349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373373 : List Nat := [1, 4, 1, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_1373373 : Nat := 118140960795 + 1373373 * 2 ^ 59
def prefixEnd_1373373 : Nat := 4983230072969 + 3 ^ 40 * 1373373 * 2
def baseEnd_1373373 : Nat := 705200466907360405521479

theorem tailTrace_1373373 : CollatzResearch.WordTrace tailWord_1373373 prefixEnd_1373373 705200466907360405521479 := by
  unfold tailWord_1373373
  simp only [CollatzResearch.WordTrace]
  refine ⟨50091028453511649279756773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33394018969007766186504515 50091028453511649279756773)
  ·
    refine ⟨9392067835033434239954395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50091028453511649279756773 9392067835033434239954395)
    ·
      refine ⟨14088101752550151359931593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9392067835033434239954395 14088101752550151359931593)
      ·
        refine ⟨10566076314412613519948695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14088101752550151359931593 10566076314412613519948695)
        ·
          refine ⟨15849114471618920279923043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10566076314412613519948695 15849114471618920279923043)
          ·
            refine ⟨23773671707428380419884565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15849114471618920279923043 23773671707428380419884565)
            ·
              refine ⟨1114390861285705332182089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23773671707428380419884565 1114390861285705332182089)
              ·
                refine ⟨835793145964278999136567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114390861285705332182089 835793145964278999136567)
                ·
                  refine ⟨1253689718946418498704851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835793145964278999136567 1253689718946418498704851)
                  ·
                    refine ⟨1880534578419627748057277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1253689718946418498704851 1880534578419627748057277)
                    ·
                      refine ⟨705200466907360405521479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1880534578419627748057277 705200466907360405521479)
                      ·
                        rfl

theorem cell23_1373373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_1373373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373373 prefixEnd_1373373 := by exact prefixLift 1373373
  have htrace : WordTrace (prefixWord ++ tailWord_1373373) baseStart_1373373 baseEnd_1373373 := by
    simpa [prefixWord, tailWord_1373373, baseEnd_1373373] using wordTrace_append hprefix tailTrace_1373373
  have hstable : (prefixWord ++ tailWord_1373373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373373).length < 2 ^ (prefixWord ++ tailWord_1373373).sum := by decide
  have hdescent : baseEnd_1373373 < baseStart_1373373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373375 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1373375 : Nat := 118140960795 + 1373375 * 2 ^ 59
def prefixEnd_1373375 : Nat := 4983230072969 + 3 ^ 40 * 1373375 * 2
def baseEnd_1373375 : Nat := 705201493868669397696469

theorem tailTrace_1373375 : CollatzResearch.WordTrace tailWord_1373375 prefixEnd_1373375 705201493868669397696469 := by
  unfold tailWord_1373375
  simp only [CollatzResearch.WordTrace]
  refine ⟨50091101399504403621329579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33394067599669602414219719 50091101399504403621329579)
  ·
    refine ⟨75136652099256605431994369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50091101399504403621329579 75136652099256605431994369)
    ·
      refine ⟨56352489074442454073995777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75136652099256605431994369 56352489074442454073995777)
      ·
        refine ⟨42264366805831840555496833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56352489074442454073995777 42264366805831840555496833)
        ·
          refine ⟨31698275104373880416622625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42264366805831840555496833 31698275104373880416622625)
          ·
            refine ⟨23773706328280410312466969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31698275104373880416622625 23773706328280410312466969)
            ·
              refine ⟨17830279746210307734350227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23773706328280410312466969 17830279746210307734350227)
              ·
                refine ⟨26745419619315461601525341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17830279746210307734350227 26745419619315461601525341)
                ·
                  refine ⟨10029532357243298100572003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26745419619315461601525341 10029532357243298100572003)
                  ·
                    refine ⟨15044298535864947150858005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10029532357243298100572003 15044298535864947150858005)
                    ·
                      refine ⟨705201493868669397696469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15044298535864947150858005 705201493868669397696469)
                      ·
                        rfl

theorem cell23_1373375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1373375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373375 prefixEnd_1373375 := by exact prefixLift 1373375
  have htrace : WordTrace (prefixWord ++ tailWord_1373375) baseStart_1373375 baseEnd_1373375 := by
    simpa [prefixWord, tailWord_1373375, baseEnd_1373375] using wordTrace_append hprefix tailTrace_1373375
  have hstable : (prefixWord ++ tailWord_1373375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373375).length < 2 ^ (prefixWord ++ tailWord_1373375).sum := by decide
  have hdescent : baseEnd_1373375 < baseStart_1373375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373413 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 1, 1, 4]
def baseStart_1373413 : Nat := 118140960795 + 1373413 * 2 ^ 59
def prefixEnd_1373413 : Nat := 4983230072969 + 3 ^ 40 * 1373413 * 2
def baseEnd_1373413 : Nat := 705221006133540249021295

theorem tailTrace_1373413 : CollatzResearch.WordTrace tailWord_1373413 prefixEnd_1373413 705221006133540249021295 := by
  unfold tailWord_1373413
  simp only [CollatzResearch.WordTrace]
  refine ⟨50092487373366736111212893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33394991582244490740808595 50092487373366736111212893)
  ·
    refine ⟨18784682765012526041704835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50092487373366736111212893 18784682765012526041704835)
    ·
      refine ⟨28177024147518789062557253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18784682765012526041704835 28177024147518789062557253)
      ·
        refine ⟨5283192027659772949229485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28177024147518789062557253 5283192027659772949229485)
        ·
          refine ⟨1981197010372414855961057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5283192027659772949229485 1981197010372414855961057)
          ·
            refine ⟨1485897757779311141970793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981197010372414855961057 1485897757779311141970793)
            ·
              refine ⟨1114423318334483356478095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485897757779311141970793 1114423318334483356478095)
              ·
                refine ⟨1671634977501725034717143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114423318334483356478095 1671634977501725034717143)
                ·
                  refine ⟨2507452466252587552075715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671634977501725034717143 2507452466252587552075715)
                  ·
                    refine ⟨3761178699378881328113573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2507452466252587552075715 3761178699378881328113573)
                    ·
                      refine ⟨705221006133540249021295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3761178699378881328113573 705221006133540249021295)
                      ·
                        rfl

theorem cell23_1373413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_1373413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373413 prefixEnd_1373413 := by exact prefixLift 1373413
  have htrace : WordTrace (prefixWord ++ tailWord_1373413) baseStart_1373413 baseEnd_1373413 := by
    simpa [prefixWord, tailWord_1373413, baseEnd_1373413] using wordTrace_append hprefix tailTrace_1373413
  have hstable : (prefixWord ++ tailWord_1373413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373413).length < 2 ^ (prefixWord ++ tailWord_1373413).sum := by decide
  have hdescent : baseEnd_1373413 < baseStart_1373413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373423 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 2, 4]
def baseStart_1373423 : Nat := 118140960795 + 1373423 * 2 ^ 59
def prefixEnd_1373423 : Nat := 4983230072969 + 3 ^ 40 * 1373423 * 2
def baseEnd_1373423 : Nat := 235075380313361736632083

theorem tailTrace_1373423 : CollatzResearch.WordTrace tailWord_1373423 prefixEnd_1373423 235075380313361736632083 := by
  unfold tailWord_1373423
  simp only [CollatzResearch.WordTrace]
  refine ⟨50092852103330507819076923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33395234735553671879384615 50092852103330507819076923)
  ·
    refine ⟨75139278154995761728615385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50092852103330507819076923 75139278154995761728615385)
    ·
      refine ⟨56354458616246821296461539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75139278154995761728615385 56354458616246821296461539)
      ·
        refine ⟨84531687924370231944692309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56354458616246821296461539 84531687924370231944692309)
        ·
          refine ⟨990605717863713655601863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 84531687924370231944692309 990605717863713655601863)
          ·
            refine ⟨1485908576795570483402795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990605717863713655601863 1485908576795570483402795)
            ·
              refine ⟨2228862865193355725104193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485908576795570483402795 2228862865193355725104193)
              ·
                refine ⟨1671647148895016793828145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228862865193355725104193 1671647148895016793828145)
                ·
                  refine ⟨1253735361671262595371109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1671647148895016793828145 1253735361671262595371109)
                  ·
                    refine ⟨235075380313361736632083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1253735361671262595371109 235075380313361736632083)
                    ·
                      rfl

theorem cell23_1373423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 4].length) (baseStart_1373423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373423 prefixEnd_1373423 := by exact prefixLift 1373423
  have htrace : WordTrace (prefixWord ++ tailWord_1373423) baseStart_1373423 baseEnd_1373423 := by
    simpa [prefixWord, tailWord_1373423, baseEnd_1373423] using wordTrace_append hprefix tailTrace_1373423
  have hstable : (prefixWord ++ tailWord_1373423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373423).length < 2 ^ (prefixWord ++ tailWord_1373423).sum := by decide
  have hdescent : baseEnd_1373423 < baseStart_1373423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373497 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1373497 : Nat := 118140960795 + 1373497 * 2 ^ 59
def prefixEnd_1373497 : Nat := 4983230072969 + 3 ^ 40 * 1373497 * 2
def baseEnd_1373497 : Nat := 705264138508517920370909

theorem tailTrace_1373497 : CollatzResearch.WordTrace tailWord_1373497 prefixEnd_1373497 705264138508517920370909 := by
  unfold tailWord_1373497
  simp only [CollatzResearch.WordTrace]
  refine ⟨50095551105062418457270745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33397034070041612304847163 50095551105062418457270745)
  ·
    refine ⟨37571663328796813842953059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50095551105062418457270745 37571663328796813842953059)
    ·
      refine ⟨56357494993195220764429589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37571663328796813842953059 56357494993195220764429589)
      ·
        refine ⟨2641757577806025973332637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56357494993195220764429589 2641757577806025973332637)
        ·
          refine ⟨990659091677259739999739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2641757577806025973332637 990659091677259739999739)
          ·
            refine ⟨1485988637515889609999609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990659091677259739999739 1485988637515889609999609)
            ·
              refine ⟨1114491478136917207499707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485988637515889609999609 1114491478136917207499707)
              ·
                refine ⟨1671737217205375811249561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114491478136917207499707 1671737217205375811249561)
                ·
                  refine ⟨1253802912904031858437171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1671737217205375811249561 1253802912904031858437171)
                  ·
                    refine ⟨1880704369356047787655757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1253802912904031858437171 1880704369356047787655757)
                    ·
                      refine ⟨705264138508517920370909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1880704369356047787655757 705264138508517920370909)
                      ·
                        rfl

theorem cell23_1373497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1373497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373497 prefixEnd_1373497 := by exact prefixLift 1373497
  have htrace : WordTrace (prefixWord ++ tailWord_1373497) baseStart_1373497 baseEnd_1373497 := by
    simpa [prefixWord, tailWord_1373497, baseEnd_1373497] using wordTrace_append hprefix tailTrace_1373497
  have hstable : (prefixWord ++ tailWord_1373497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373497).length < 2 ^ (prefixWord ++ tailWord_1373497).sum := by decide
  have hdescent : baseEnd_1373497 < baseStart_1373497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373503 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 2, 2, 2]
def baseStart_1373503 : Nat := 118140960795 + 1373503 * 2 ^ 59
def prefixEnd_1373503 : Nat := 4983230072969 + 3 ^ 40 * 1373503 * 2
def baseEnd_1373503 : Nat := 705267219392444896895881

theorem tailTrace_1373503 : CollatzResearch.WordTrace tailWord_1373503 prefixEnd_1373503 705267219392444896895881 := by
  unfold tailWord_1373503
  simp only [CollatzResearch.WordTrace]
  refine ⟨50095769943040681481989163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33397179962027120987992775 50095769943040681481989163)
  ·
    refine ⟨75143654914561022222983745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50095769943040681481989163 75143654914561022222983745)
    ·
      refine ⟨56357741185920766667237809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75143654914561022222983745 56357741185920766667237809)
      ·
        refine ⟨42268305889440575000428357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56357741185920766667237809 42268305889440575000428357)
        ·
          refine ⟨7925307354270107812580317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42268305889440575000428357 7925307354270107812580317)
          ·
            refine ⟨2971990257851290429717619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7925307354270107812580317 2971990257851290429717619)
            ·
              refine ⟨4457985386776935644576429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971990257851290429717619 4457985386776935644576429)
              ·
                refine ⟨1671744520041350866716161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4457985386776935644576429 1671744520041350866716161)
                ·
                  refine ⟨1253808390031013150037121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1671744520041350866716161 1253808390031013150037121)
                  ·
                    refine ⟨940356292523259862527841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1253808390031013150037121 940356292523259862527841)
                    ·
                      refine ⟨705267219392444896895881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940356292523259862527841 705267219392444896895881)
                      ·
                        rfl

theorem cell23_1373503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_1373503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373503 prefixEnd_1373503 := by exact prefixLift 1373503
  have htrace : WordTrace (prefixWord ++ tailWord_1373503) baseStart_1373503 baseEnd_1373503 := by
    simpa [prefixWord, tailWord_1373503, baseEnd_1373503] using wordTrace_append hprefix tailTrace_1373503
  have hstable : (prefixWord ++ tailWord_1373503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373503).length < 2 ^ (prefixWord ++ tailWord_1373503).sum := by decide
  have hdescent : baseEnd_1373503 < baseStart_1373503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373539 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 2, 5]
def baseStart_1373539 : Nat := 118140960795 + 1373539 * 2 ^ 59
def prefixEnd_1373539 : Nat := 4983230072969 + 3 ^ 40 * 1373539 * 2
def baseEnd_1373539 : Nat := 235095234898668918681905

theorem tailTrace_1373539 : CollatzResearch.WordTrace tailWord_1373539 prefixEnd_1373539 235095234898668918681905 := by
  unfold tailWord_1373539
  simp only [CollatzResearch.WordTrace]
  refine ⟨50097082970910259630299671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33398055313940173086866447 50097082970910259630299671)
  ·
    refine ⟨75145624456365389445449507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50097082970910259630299671 75145624456365389445449507)
    ·
      refine ⟨112718436684548084168174261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75145624456365389445449507 112718436684548084168174261)
      ·
        refine ⟨10567353439176382890766337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112718436684548084168174261 10567353439176382890766337)
        ·
          refine ⟨7925515079382287168074753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10567353439176382890766337 7925515079382287168074753)
          ·
            refine ⟨5944136309536715376056065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7925515079382287168074753 5944136309536715376056065)
            ·
              refine ⟨4458102232152536532042049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5944136309536715376056065 4458102232152536532042049)
              ·
                refine ⟨3343576674114402399031537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4458102232152536532042049 3343576674114402399031537)
                ·
                  refine ⟨2507682505585801799273653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343576674114402399031537 2507682505585801799273653)
                  ·
                    refine ⟨235095234898668918681905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2507682505585801799273653 235095234898668918681905)
                    ·
                      rfl

theorem cell23_1373539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 5].length) (baseStart_1373539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373539 prefixEnd_1373539 := by exact prefixLift 1373539
  have htrace : WordTrace (prefixWord ++ tailWord_1373539) baseStart_1373539 baseEnd_1373539 := by
    simpa [prefixWord, tailWord_1373539, baseEnd_1373539] using wordTrace_append hprefix tailTrace_1373539
  have hstable : (prefixWord ++ tailWord_1373539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373539).length < 2 ^ (prefixWord ++ tailWord_1373539).sum := by decide
  have hdescent : baseEnd_1373539 < baseStart_1373539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373549 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1373549 : Nat := 118140960795 + 1373549 * 2 ^ 59
def prefixEnd_1373549 : Nat := 4983230072969 + 3 ^ 40 * 1373549 * 2
def baseEnd_1373549 : Nat := 705290839502551716920669

theorem tailTrace_1373549 : CollatzResearch.WordTrace tailWord_1373549 prefixEnd_1373549 705290839502551716920669 := by
  unfold tailWord_1373549
  simp only [CollatzResearch.WordTrace]
  refine ⟨50097447700874031338163701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33398298467249354225442467 50097447700874031338163701)
  ·
    refine ⟨4696635721956940437952847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50097447700874031338163701 4696635721956940437952847)
    ·
      refine ⟨7044953582935410656929271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4696635721956940437952847 7044953582935410656929271)
      ·
        refine ⟨10567430374403115985393907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7044953582935410656929271 10567430374403115985393907)
        ·
          refine ⟨15851145561604673978090861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10567430374403115985393907 15851145561604673978090861)
          ·
            refine ⟨5944179585601752741784073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15851145561604673978090861 5944179585601752741784073)
            ·
              refine ⟨4458134689201314556338055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5944179585601752741784073 4458134689201314556338055)
              ·
                refine ⟨6687202033801971834507083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458134689201314556338055 6687202033801971834507083)
                ·
                  refine ⟨10030803050702957751760625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6687202033801971834507083 10030803050702957751760625)
                  ·
                    refine ⟨7523102288027218313820469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10030803050702957751760625 7523102288027218313820469)
                    ·
                      refine ⟨705290839502551716920669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7523102288027218313820469 705290839502551716920669)
                      ·
                        rfl

theorem cell23_1373549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1373549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373549 prefixEnd_1373549 := by exact prefixLift 1373549
  have htrace : WordTrace (prefixWord ++ tailWord_1373549) baseStart_1373549 baseEnd_1373549 := by
    simpa [prefixWord, tailWord_1373549, baseEnd_1373549] using wordTrace_append hprefix tailTrace_1373549
  have hstable : (prefixWord ++ tailWord_1373549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373549).length < 2 ^ (prefixWord ++ tailWord_1373549).sum := by decide
  have hdescent : baseEnd_1373549 < baseStart_1373549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373562 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_1373562 : Nat := 118140960795 + 1373562 * 2 ^ 59
def prefixEnd_1373562 : Nat := 4983230072969 + 3 ^ 40 * 1373562 * 2
def baseEnd_1373562 : Nat := 705297514751060166058109

theorem tailTrace_1373562 : CollatzResearch.WordTrace tailWord_1373562 prefixEnd_1373562 705297514751060166058109 := by
  unfold tailWord_1373562
  simp only [CollatzResearch.WordTrace]
  refine ⟨12524480462456733639596735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33398614566551289705591293 12524480462456733639596735)
  ·
    refine ⟨18786720693685100459395103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12524480462456733639596735 18786720693685100459395103)
    ·
      refine ⟨28180081040527650689092655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18786720693685100459395103 28180081040527650689092655)
      ·
        refine ⟨42270121560791476033638983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28180081040527650689092655 42270121560791476033638983)
        ·
          refine ⟨63405182341187214050458475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42270121560791476033638983 63405182341187214050458475)
          ·
            refine ⟨95107773511780821075687713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63405182341187214050458475 95107773511780821075687713)
            ·
              refine ⟨71330830133835615806765785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95107773511780821075687713 71330830133835615806765785)
              ·
                refine ⟨53498122600376711855074339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71330830133835615806765785 53498122600376711855074339)
                ·
                  refine ⟨80247183900565067782611509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53498122600376711855074339 80247183900565067782611509)
                  ·
                    refine ⟨7523173490677975104619829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80247183900565067782611509 7523173490677975104619829)
                    ·
                      refine ⟨705297514751060166058109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7523173490677975104619829 705297514751060166058109)
                      ·
                        rfl

theorem cell23_1373562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_1373562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373562 prefixEnd_1373562 := by exact prefixLift 1373562
  have htrace : WordTrace (prefixWord ++ tailWord_1373562) baseStart_1373562 baseEnd_1373562 := by
    simpa [prefixWord, tailWord_1373562, baseEnd_1373562] using wordTrace_append hprefix tailTrace_1373562
  have hstable : (prefixWord ++ tailWord_1373562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373562).length < 2 ^ (prefixWord ++ tailWord_1373562).sum := by decide
  have hdescent : baseEnd_1373562 < baseStart_1373562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373576 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1373576 : Nat := 118140960795 + 1373576 * 2 ^ 59
def prefixEnd_1373576 : Nat := 4983230072969 + 3 ^ 40 * 1373576 * 2
def baseEnd_1373576 : Nat := 705304703480223111283045

theorem tailTrace_1373576 : CollatzResearch.WordTrace tailWord_1373576 prefixEnd_1373576 705304703480223111283045 := by
  unfold tailWord_1373576
  simp only [CollatzResearch.WordTrace]
  refine ⟨25049216235888107474698291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33398954981184143299597721 25049216235888107474698291)
  ·
    refine ⟨37573824353832161212047437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25049216235888107474698291 37573824353832161212047437)
    ·
      refine ⟨14090184132687060454517789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37573824353832161212047437 14090184132687060454517789)
      ·
        refine ⟨5283819049757647670444171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14090184132687060454517789 5283819049757647670444171)
        ·
          refine ⟨7925728574636471505666257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283819049757647670444171 7925728574636471505666257)
          ·
            refine ⟨5944296430977353629249693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7925728574636471505666257 5944296430977353629249693)
            ·
              refine ⟨2229111161616507610968635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5944296430977353629249693 2229111161616507610968635)
              ·
                refine ⟨3343666742424761416452953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229111161616507610968635 3343666742424761416452953)
                ·
                  refine ⟨2507750056818571062339715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343666742424761416452953 2507750056818571062339715)
                  ·
                    refine ⟨3761625085227856593509573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2507750056818571062339715 3761625085227856593509573)
                    ·
                      refine ⟨705304703480223111283045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3761625085227856593509573 705304703480223111283045)
                      ·
                        rfl

theorem cell23_1373576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1373576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373576 prefixEnd_1373576 := by exact prefixLift 1373576
  have htrace : WordTrace (prefixWord ++ tailWord_1373576) baseStart_1373576 baseEnd_1373576 := by
    simpa [prefixWord, tailWord_1373576, baseEnd_1373576] using wordTrace_append hprefix tailTrace_1373576
  have hstable : (prefixWord ++ tailWord_1373576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373576).length < 2 ^ (prefixWord ++ tailWord_1373576).sum := by decide
  have hdescent : baseEnd_1373576 < baseStart_1373576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373579 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 3]
def baseStart_1373579 : Nat := 118140960795 + 1373579 * 2 ^ 59
def prefixEnd_1373579 : Nat := 4983230072969 + 3 ^ 40 * 1373579 * 2
def baseEnd_1373579 : Nat := 705306243922186599545531

theorem tailTrace_1373579 : CollatzResearch.WordTrace tailWord_1373579 prefixEnd_1373579 705306243922186599545531 := by
  unfold tailWord_1373579
  simp only [CollatzResearch.WordTrace]
  refine ⟨50098541890765346461755791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33399027927176897641170527 50098541890765346461755791)
  ·
    refine ⟨75147812836148019692633687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50098541890765346461755791 75147812836148019692633687)
    ·
      refine ⟨112721719254222029538950531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75147812836148019692633687 112721719254222029538950531)
      ·
        refine ⟨169082578881333044308425797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112721719254222029538950531 169082578881333044308425797)
        ·
          refine ⟨31702983540249945807829837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169082578881333044308425797 31702983540249945807829837)
          ·
            refine ⟨11888618827593729677936189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31702983540249945807829837 11888618827593729677936189)
            ·
              refine ⟨4458232060347648629226071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11888618827593729677936189 4458232060347648629226071)
              ·
                refine ⟨6687348090521472943839107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458232060347648629226071 6687348090521472943839107)
                ·
                  refine ⟨10031022135782209415758661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6687348090521472943839107 10031022135782209415758661)
                  ·
                    refine ⟨1880816650459164265454749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10031022135782209415758661 1880816650459164265454749)
                    ·
                      refine ⟨705306243922186599545531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1880816650459164265454749 705306243922186599545531)
                      ·
                        rfl

theorem cell23_1373579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 3].length) (baseStart_1373579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373579 prefixEnd_1373579 := by exact prefixLift 1373579
  have htrace : WordTrace (prefixWord ++ tailWord_1373579) baseStart_1373579 baseEnd_1373579 := by
    simpa [prefixWord, tailWord_1373579, baseEnd_1373579] using wordTrace_append hprefix tailTrace_1373579
  have hstable : (prefixWord ++ tailWord_1373579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373579).length < 2 ^ (prefixWord ++ tailWord_1373579).sum := by decide
  have hdescent : baseEnd_1373579 < baseStart_1373579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373599 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 8]
def baseStart_1373599 : Nat := 118140960795 + 1373599 * 2 ^ 59
def prefixEnd_1373599 : Nat := 4983230072969 + 3 ^ 40 * 1373599 * 2
def baseEnd_1373599 : Nat := 78368501503919613477271

theorem tailTrace_1373599 : CollatzResearch.WordTrace tailWord_1373599 prefixEnd_1373599 78368501503919613477271 := by
  unfold tailWord_1373599
  simp only [CollatzResearch.WordTrace]
  refine ⟨50099271350692889877483851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33399514233795259918322567 50099271350692889877483851)
  ·
    refine ⟨75148907026039334816225777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50099271350692889877483851 75148907026039334816225777)
    ·
      refine ⟨56361680269529501112169333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75148907026039334816225777 56361680269529501112169333)
      ·
        refine ⟨5283907525268390729265875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56361680269529501112169333 5283907525268390729265875)
        ·
          refine ⟨7925861287902586093898813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283907525268390729265875 7925861287902586093898813)
          ·
            refine ⟨2972197982963469785212055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7925861287902586093898813 2972197982963469785212055)
            ·
              refine ⟨4458296974445204677818083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972197982963469785212055 4458296974445204677818083)
              ·
                refine ⟨6687445461667807016727125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458296974445204677818083 6687445461667807016727125)
                ·
                  refine ⟨78368501503919613477271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6687445461667807016727125 78368501503919613477271)
                  ·
                    rfl

theorem cell23_1373599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 8].length) (baseStart_1373599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373599 prefixEnd_1373599 := by exact prefixLift 1373599
  have htrace : WordTrace (prefixWord ++ tailWord_1373599) baseStart_1373599 baseEnd_1373599 := by
    simpa [prefixWord, tailWord_1373599, baseEnd_1373599] using wordTrace_append hprefix tailTrace_1373599
  have hstable : (prefixWord ++ tailWord_1373599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373599).length < 2 ^ (prefixWord ++ tailWord_1373599).sum := by decide
  have hdescent : baseEnd_1373599 < baseStart_1373599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373646 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_1373646 : Nat := 118140960795 + 1373646 * 2 ^ 59
def prefixEnd_1373646 : Nat := 4983230072969 + 3 ^ 40 * 1373646 * 2
def baseEnd_1373646 : Nat := 235113549042012612469241

theorem tailTrace_1373646 : CollatzResearch.WordTrace tailWord_1373646 prefixEnd_1373646 235113549042012612469241 := by
  unfold tailWord_1373646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262623197690327113055599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33400657054348411269629861 6262623197690327113055599)
  ·
    refine ⟨9393934796535490669583399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262623197690327113055599 9393934796535490669583399)
    ·
      refine ⟨14090902194803236004375099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9393934796535490669583399 14090902194803236004375099)
      ·
        refine ⟨21136353292204854006562649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14090902194803236004375099 21136353292204854006562649)
        ·
          refine ⟨15852264969153640504921987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21136353292204854006562649 15852264969153640504921987)
          ·
            refine ⟨23778397453730460757382981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15852264969153640504921987 23778397453730460757382981)
            ·
              refine ⟨4458449522574461392009309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23778397453730460757382981 4458449522574461392009309)
              ·
                refine ⟨1671918570965423022003491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4458449522574461392009309 1671918570965423022003491)
                ·
                  refine ⟨2507877856448134533005237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671918570965423022003491 2507877856448134533005237)
                  ·
                    refine ⟨235113549042012612469241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2507877856448134533005237 235113549042012612469241)
                    ·
                      rfl

theorem cell23_1373646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_1373646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373646 prefixEnd_1373646 := by exact prefixLift 1373646
  have htrace : WordTrace (prefixWord ++ tailWord_1373646) baseStart_1373646 baseEnd_1373646 := by
    simpa [prefixWord, tailWord_1373646, baseEnd_1373646] using wordTrace_append hprefix tailTrace_1373646
  have hstable : (prefixWord ++ tailWord_1373646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373646).length < 2 ^ (prefixWord ++ tailWord_1373646).sum := by decide
  have hdescent : baseEnd_1373646 < baseStart_1373646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373649 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_1373649 : Nat := 118140960795 + 1373649 * 2 ^ 59
def prefixEnd_1373649 : Nat := 4983230072969 + 3 ^ 40 * 1373649 * 2
def baseEnd_1373649 : Nat := 705342187568001325670209

theorem tailTrace_1373649 : CollatzResearch.WordTrace tailWord_1373649 prefixEnd_1373649 705342187568001325670209 := by
  unfold tailWord_1373649
  simp only [CollatzResearch.WordTrace]
  refine ⟨50101095000511748416804001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33400730000341165611202667 50101095000511748416804001)
  ·
    refine ⟨37575821250383811312603001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50101095000511748416804001 37575821250383811312603001)
    ·
      refine ⟨28181865937787858484452251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37575821250383811312603001 28181865937787858484452251)
      ·
        refine ⟨42272798906681787726678377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28181865937787858484452251 42272798906681787726678377)
        ·
          refine ⟨31704599180011340795008783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42272798906681787726678377 31704599180011340795008783)
          ·
            refine ⟨47556898770017011192513175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31704599180011340795008783 47556898770017011192513175)
            ·
              refine ⟨71335348155025516788769763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47556898770017011192513175 71335348155025516788769763)
              ·
                refine ⟨107003022232538275183154645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71335348155025516788769763 107003022232538275183154645)
                ·
                  refine ⟨2507883333575115824605187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 107003022232538275183154645 2507883333575115824605187)
                  ·
                    refine ⟨3761825000362673736907781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2507883333575115824605187 3761825000362673736907781)
                    ·
                      refine ⟨705342187568001325670209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3761825000362673736907781 705342187568001325670209)
                      ·
                        rfl

theorem cell23_1373649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_1373649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373649 prefixEnd_1373649 := by exact prefixLift 1373649
  have htrace : WordTrace (prefixWord ++ tailWord_1373649) baseStart_1373649 baseEnd_1373649 := by
    simpa [prefixWord, tailWord_1373649, baseEnd_1373649] using wordTrace_append hprefix tailTrace_1373649
  have hstable : (prefixWord ++ tailWord_1373649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373649).length < 2 ^ (prefixWord ++ tailWord_1373649).sum := by decide
  have hdescent : baseEnd_1373649 < baseStart_1373649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373653 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_1373653 : Nat := 118140960795 + 1373653 * 2 ^ 59
def prefixEnd_1373653 : Nat := 4983230072969 + 3 ^ 40 * 1373653 * 2
def baseEnd_1373653 : Nat := 705344241490619310020191

theorem tailTrace_1373653 : CollatzResearch.WordTrace tailWord_1373653 prefixEnd_1373653 705344241490619310020191 := by
  unfold tailWord_1373653
  simp only [CollatzResearch.WordTrace]
  refine ⟨50101240892497257099949613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33400827261664838066633075 50101240892497257099949613)
  ·
    refine ⟨18787965334686471412481105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50101240892497257099949613 18787965334686471412481105)
    ·
      refine ⟨14090974001014853559360829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18787965334686471412481105 14090974001014853559360829)
      ·
        refine ⟨5284115250380570084760311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14090974001014853559360829 5284115250380570084760311)
        ·
          refine ⟨7926172875570855127140467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284115250380570084760311 7926172875570855127140467)
          ·
            refine ⟨11889259313356282690710701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926172875570855127140467 11889259313356282690710701)
            ·
              refine ⟨4458472242508606009016513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11889259313356282690710701 4458472242508606009016513)
              ·
                refine ⟨3343854181881454506762385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4458472242508606009016513 3343854181881454506762385)
                ·
                  refine ⟨2507890636411090880071789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343854181881454506762385 2507890636411090880071789)
                  ·
                    refine ⟨940458988654159080026921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507890636411090880071789 940458988654159080026921)
                    ·
                      refine ⟨705344241490619310020191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940458988654159080026921 705344241490619310020191)
                      ·
                        rfl

theorem cell23_1373653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_1373653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373653 prefixEnd_1373653 := by exact prefixLift 1373653
  have htrace : WordTrace (prefixWord ++ tailWord_1373653) baseStart_1373653 baseEnd_1373653 := by
    simpa [prefixWord, tailWord_1373653, baseEnd_1373653] using wordTrace_append hprefix tailTrace_1373653
  have hstable : (prefixWord ++ tailWord_1373653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373653).length < 2 ^ (prefixWord ++ tailWord_1373653).sum := by decide
  have hdescent : baseEnd_1373653 < baseStart_1373653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373679 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_1373679 : Nat := 118140960795 + 1373679 * 2 ^ 59
def prefixEnd_1373679 : Nat := 4983230072969 + 3 ^ 40 * 1373679 * 2
def baseEnd_1373679 : Nat := 705357591987636208295071

theorem tailTrace_1373679 : CollatzResearch.WordTrace tailWord_1373679 prefixEnd_1373679 705357591987636208295071 := by
  unfold tailWord_1373679
  simp only [CollatzResearch.WordTrace]
  refine ⟨50102189190403063540396091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33401459460268709026930727 50102189190403063540396091)
  ·
    refine ⟨75153283785604595310594137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50102189190403063540396091 75153283785604595310594137)
    ·
      refine ⟨56364962839203446482945603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75153283785604595310594137 56364962839203446482945603)
      ·
        refine ⟨84547444258805169724418405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56364962839203446482945603 84547444258805169724418405)
        ·
          refine ⟨15852645798525969323328451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84547444258805169724418405 15852645798525969323328451)
          ·
            refine ⟨23778968697788953984992677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15852645798525969323328451 23778968697788953984992677)
            ·
              refine ⟨4458556630835428872186127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23778968697788953984992677 4458556630835428872186127)
              ·
                refine ⟨6687834946253143308279191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458556630835428872186127 6687834946253143308279191)
                ·
                  refine ⟨10031752419379714962418787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6687834946253143308279191 10031752419379714962418787)
                  ·
                    refine ⟨15047628629069572443628181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10031752419379714962418787 15047628629069572443628181)
                    ·
                      refine ⟨705357591987636208295071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15047628629069572443628181 705357591987636208295071)
                      ·
                        rfl

theorem cell23_1373679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_1373679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373679 prefixEnd_1373679 := by exact prefixLift 1373679
  have htrace : WordTrace (prefixWord ++ tailWord_1373679) baseStart_1373679 baseEnd_1373679 := by
    simpa [prefixWord, tailWord_1373679, baseEnd_1373679] using wordTrace_append hprefix tailTrace_1373679
  have hstable : (prefixWord ++ tailWord_1373679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373679).length < 2 ^ (prefixWord ++ tailWord_1373679).sum := by decide
  have hdescent : baseEnd_1373679 < baseStart_1373679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373703 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1373703 : Nat := 118140960795 + 1373703 * 2 ^ 59
def prefixEnd_1373703 : Nat := 4983230072969 + 3 ^ 40 * 1373703 * 2
def baseEnd_1373703 : Nat := 705369915523344114394961

theorem tailTrace_1373703 : CollatzResearch.WordTrace tailWord_1373703 prefixEnd_1373703 705369915523344114394961 := by
  unfold tailWord_1373703
  simp only [CollatzResearch.WordTrace]
  refine ⟨50103064542316115639269763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33402043028210743759513175 50103064542316115639269763)
  ·
    refine ⟨75154596813474173458904645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50103064542316115639269763 75154596813474173458904645)
    ·
      refine ⟨14091486902526407523544621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75154596813474173458904645 14091486902526407523544621)
      ·
        refine ⟨5284307588447402821329233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14091486902526407523544621 5284307588447402821329233)
        ·
          refine ⟨3963230691335552115996925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5284307588447402821329233 3963230691335552115996925)
          ·
            refine ⟨1486211509250832043498847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3963230691335552115996925 1486211509250832043498847)
            ·
              refine ⟨2229317263876248065248271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486211509250832043498847 2229317263876248065248271)
              ·
                refine ⟨3343975895814372097872407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229317263876248065248271 3343975895814372097872407)
                ·
                  refine ⟨5015963843721558146808611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343975895814372097872407 5015963843721558146808611)
                  ·
                    refine ⟨7523945765582337220212917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5015963843721558146808611 7523945765582337220212917)
                    ·
                      refine ⟨705369915523344114394961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7523945765582337220212917 705369915523344114394961)
                      ·
                        rfl

theorem cell23_1373703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1373703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373703 prefixEnd_1373703 := by exact prefixLift 1373703
  have htrace : WordTrace (prefixWord ++ tailWord_1373703) baseStart_1373703 baseEnd_1373703 := by
    simpa [prefixWord, tailWord_1373703, baseEnd_1373703] using wordTrace_append hprefix tailTrace_1373703
  have hstable : (prefixWord ++ tailWord_1373703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373703).length < 2 ^ (prefixWord ++ tailWord_1373703).sum := by decide
  have hdescent : baseEnd_1373703 < baseStart_1373703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373710 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_1373710 : Nat := 118140960795 + 1373710 * 2 ^ 59
def prefixEnd_1373710 : Nat := 4983230072969 + 3 ^ 40 * 1373710 * 2
def baseEnd_1373710 : Nat := 235124503295975195669143

theorem tailTrace_1373710 : CollatzResearch.WordTrace tailWord_1373710 prefixEnd_1373710 235124503295975195669143 := by
  unfold tailWord_1373710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262914981661344479346823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33402213235527170556516389 6262914981661344479346823)
  ·
    refine ⟨9394372472492016719020235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262914981661344479346823 9394372472492016719020235)
    ·
      refine ⟨14091558708738025078530353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9394372472492016719020235 14091558708738025078530353)
      ·
        refine ⟨10568669031553518808897765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14091558708738025078530353 10568669031553518808897765)
        ·
          refine ⟨1981625443416284776668331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10568669031553518808897765 1981625443416284776668331)
          ·
            refine ⟨2972438165124427165002497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981625443416284776668331 2972438165124427165002497)
            ·
              refine ⟨2229328623843320373751873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2972438165124427165002497 2229328623843320373751873)
              ·
                refine ⟨1671996467882490280313905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229328623843320373751873 1671996467882490280313905)
                ·
                  refine ⟨1253997350911867710235429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1671996467882490280313905 1253997350911867710235429)
                  ·
                    refine ⟨235124503295975195669143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1253997350911867710235429 235124503295975195669143)
                    ·
                      rfl

theorem cell23_1373710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_1373710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373710 prefixEnd_1373710 := by exact prefixLift 1373710
  have htrace : WordTrace (prefixWord ++ tailWord_1373710) baseStart_1373710 baseEnd_1373710 := by
    simpa [prefixWord, tailWord_1373710, baseEnd_1373710] using wordTrace_append hprefix tailTrace_1373710
  have hstable : (prefixWord ++ tailWord_1373710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373710).length < 2 ^ (prefixWord ++ tailWord_1373710).sum := by decide
  have hdescent : baseEnd_1373710 < baseStart_1373710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373717 : List Nat := [1, 3, 2, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_1373717 : Nat := 118140960795 + 1373717 * 2 ^ 59
def prefixEnd_1373717 : Nat := 4983230072969 + 3 ^ 40 * 1373717 * 2
def baseEnd_1373717 : Nat := 705377104252507059619897

theorem tailTrace_1373717 : CollatzResearch.WordTrace tailWord_1373717 prefixEnd_1373717 705377104252507059619897 := by
  unfold tailWord_1373717
  simp only [CollatzResearch.WordTrace]
  refine ⟨50103575164265396030279405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33402383442843597353519603 50103575164265396030279405)
  ·
    refine ⟨18788840686599523511354777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50103575164265396030279405 18788840686599523511354777)
    ·
      refine ⟨14091630514949642633516083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18788840686599523511354777 14091630514949642633516083)
      ·
        refine ⟨21137445772424463950274125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14091630514949642633516083 21137445772424463950274125)
        ·
          refine ⟨7926542164659173981352797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21137445772424463950274125 7926542164659173981352797)
          ·
            refine ⟨2972453311747190243007299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7926542164659173981352797 2972453311747190243007299)
            ·
              refine ⟨4458679967620785364510949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972453311747190243007299 4458679967620785364510949)
              ·
                refine ⟨836002493928897255845803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4458679967620785364510949 836002493928897255845803)
                ·
                  refine ⟨1254003740893345883768705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836002493928897255845803 1254003740893345883768705)
                  ·
                    refine ⟨940502805670009412826529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1254003740893345883768705 940502805670009412826529)
                    ·
                      refine ⟨705377104252507059619897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940502805670009412826529 705377104252507059619897)
                      ·
                        rfl

theorem cell23_1373717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_1373717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373717 prefixEnd_1373717 := by exact prefixLift 1373717
  have htrace : WordTrace (prefixWord ++ tailWord_1373717) baseStart_1373717 baseEnd_1373717 := by
    simpa [prefixWord, tailWord_1373717, baseEnd_1373717] using wordTrace_append hprefix tailTrace_1373717
  have hstable : (prefixWord ++ tailWord_1373717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373717).length < 2 ^ (prefixWord ++ tailWord_1373717).sum := by decide
  have hdescent : baseEnd_1373717 < baseStart_1373717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373767 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_1373767 : Nat := 118140960795 + 1373767 * 2 ^ 59
def prefixEnd_1373767 : Nat := 4983230072969 + 3 ^ 40 * 1373767 * 2
def baseEnd_1373767 : Nat := 705402778285231863994667

theorem tailTrace_1373767 : CollatzResearch.WordTrace tailWord_1373767 prefixEnd_1373767 705402778285231863994667 := by
  unfold tailWord_1373767
  simp only [CollatzResearch.WordTrace]
  refine ⟨50105398814084254569599555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33403599209389503046399703 50105398814084254569599555)
  ·
    refine ⟨75158098221126381854399333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50105398814084254569599555 75158098221126381854399333)
    ·
      refine ⟨14092143416461196597699875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75158098221126381854399333 14092143416461196597699875)
      ·
        refine ⟨21138215124691794896549813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14092143416461196597699875 21138215124691794896549813)
        ·
          refine ⟨1981707667939855771551545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21138215124691794896549813 1981707667939855771551545)
          ·
            refine ⟨1486280750954891828663659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981707667939855771551545 1486280750954891828663659)
            ·
              refine ⟨2229421126432337742995489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486280750954891828663659 2229421126432337742995489)
              ·
                refine ⟨1672065844824253307246617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229421126432337742995489 1672065844824253307246617)
                ·
                  refine ⟨1254049383618189980434963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1672065844824253307246617 1254049383618189980434963)
                  ·
                    refine ⟨1881074075427284970652445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1254049383618189980434963 1881074075427284970652445)
                    ·
                      refine ⟨705402778285231863994667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1881074075427284970652445 705402778285231863994667)
                      ·
                        rfl

theorem cell23_1373767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_1373767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373767 prefixEnd_1373767 := by exact prefixLift 1373767
  have htrace : WordTrace (prefixWord ++ tailWord_1373767) baseStart_1373767 baseEnd_1373767 := by
    simpa [prefixWord, tailWord_1373767, baseEnd_1373767] using wordTrace_append hprefix tailTrace_1373767
  have hstable : (prefixWord ++ tailWord_1373767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373767).length < 2 ^ (prefixWord ++ tailWord_1373767).sum := by decide
  have hdescent : baseEnd_1373767 < baseStart_1373767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373796 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 7]
def baseStart_1373796 : Nat := 118140960795 + 1373796 * 2 ^ 59
def prefixEnd_1373796 : Nat := 4983230072969 + 3 ^ 40 * 1373796 * 2
def baseEnd_1373796 : Nat := 78379741024912472281337

theorem tailTrace_1373796 : CollatzResearch.WordTrace tailWord_1373796 prefixEnd_1373796 78379741024912472281337 := by
  unfold tailWord_1373796
  simp only [CollatzResearch.WordTrace]
  refine ⟨25053228265489596261202621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33404304353986128348270161 25053228265489596261202621)
  ·
    refine ⟨9394960599558598597950983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25053228265489596261202621 9394960599558598597950983)
    ·
      refine ⟨14092440899337897896926475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9394960599558598597950983 14092440899337897896926475)
      ·
        refine ⟨21138661349006846845389713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14092440899337897896926475 21138661349006846845389713)
        ·
          refine ⟨15853996011755135134042285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21138661349006846845389713 15853996011755135134042285)
          ·
            refine ⟨5945248504408175675265857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15853996011755135134042285 5945248504408175675265857)
            ·
              refine ⟨4458936378306131756449393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5945248504408175675265857 4458936378306131756449393)
              ·
                refine ⟨3344202283729598817337045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4458936378306131756449393 3344202283729598817337045)
                ·
                  refine ⟨78379741024912472281337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3344202283729598817337045 78379741024912472281337)
                  ·
                    rfl

theorem cell23_1373796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_1373796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373796 prefixEnd_1373796 := by exact prefixLift 1373796
  have htrace : WordTrace (prefixWord ++ tailWord_1373796) baseStart_1373796 baseEnd_1373796 := by
    simpa [prefixWord, tailWord_1373796, baseEnd_1373796] using wordTrace_append hprefix tailTrace_1373796
  have hstable : (prefixWord ++ tailWord_1373796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373796).length < 2 ^ (prefixWord ++ tailWord_1373796).sum := by decide
  have hdescent : baseEnd_1373796 < baseStart_1373796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373836 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1373836 : Nat := 118140960795 + 1373836 * 2 ^ 59
def prefixEnd_1373836 : Nat := 4983230072969 + 3 ^ 40 * 1373836 * 2
def baseEnd_1373836 : Nat := 705438208450392094031849

theorem tailTrace_1373836 : CollatzResearch.WordTrace tailWord_1373836 prefixEnd_1373836 705438208450392094031849 := by
  unfold tailWord_1373836
  simp only [CollatzResearch.WordTrace]
  refine ⟨25053957725417139676930681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33405276967222852902574241 25053957725417139676930681)
  ·
    refine ⟨18790468294062854757698011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25053957725417139676930681 18790468294062854757698011)
    ·
      refine ⟨28185702441094282136547017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18790468294062854757698011 28185702441094282136547017)
      ·
        refine ⟨21139276830820711602410263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28185702441094282136547017 21139276830820711602410263)
        ·
          refine ⟨31708915246231067403615395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21139276830820711602410263 31708915246231067403615395)
          ·
            refine ⟨47563372869346601105423093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31708915246231067403615395 47563372869346601105423093)
            ·
              refine ⟨4459066206501243853633415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47563372869346601105423093 4459066206501243853633415)
              ·
                refine ⟨6688599309751865780450123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4459066206501243853633415 6688599309751865780450123)
                ·
                  refine ⟨10032898964627798670675185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6688599309751865780450123 10032898964627798670675185)
                  ·
                    refine ⟨7524674223470849003006389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10032898964627798670675185 7524674223470849003006389)
                    ·
                      refine ⟨705438208450392094031849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7524674223470849003006389 705438208450392094031849)
                      ·
                        rfl

theorem cell23_1373836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1373836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373836 prefixEnd_1373836 := by exact prefixLift 1373836
  have htrace : WordTrace (prefixWord ++ tailWord_1373836) baseStart_1373836 baseEnd_1373836 := by
    simpa [prefixWord, tailWord_1373836, baseEnd_1373836] using wordTrace_append hprefix tailTrace_1373836
  have hstable : (prefixWord ++ tailWord_1373836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373836).length < 2 ^ (prefixWord ++ tailWord_1373836).sum := by decide
  have hdescent : baseEnd_1373836 < baseStart_1373836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373917 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1373917 : Nat := 118140960795 + 1373917 * 2 ^ 59
def prefixEnd_1373917 : Nat := 4983230072969 + 3 ^ 40 * 1373917 * 2
def baseEnd_1373917 : Nat := 705479800383406277118977

theorem tailTrace_1373917 : CollatzResearch.WordTrace tailWord_1373917 prefixEnd_1373917 705479800383406277118977 := by
  unfold tailWord_1373917
  simp only [CollatzResearch.WordTrace]
  refine ⟨50110869763540830187560005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33407246509027220125040003 50110869763540830187560005)
  ·
    refine ⟨9395788080663905660167501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50110869763540830187560005 9395788080663905660167501)
    ·
      refine ⟨3523420530248964622562813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9395788080663905660167501 3523420530248964622562813)
      ·
        refine ⟨1321282698843361733461055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3523420530248964622562813 1321282698843361733461055)
        ·
          refine ⟨1981924048265042600191583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321282698843361733461055 1981924048265042600191583)
          ·
            refine ⟨2972886072397563900287375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981924048265042600191583 2972886072397563900287375)
            ·
              refine ⟨4459329108596345850431063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972886072397563900287375 4459329108596345850431063)
              ·
                refine ⟨6688993662894518775646595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4459329108596345850431063 6688993662894518775646595)
                ·
                  refine ⟨10033490494341778163469893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6688993662894518775646595 10033490494341778163469893)
                  ·
                    refine ⟨1881279467689083405650605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10033490494341778163469893 1881279467689083405650605)
                    ·
                      refine ⟨705479800383406277118977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1881279467689083405650605 705479800383406277118977)
                      ·
                        rfl

theorem cell23_1373917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1373917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373917 prefixEnd_1373917 := by exact prefixLift 1373917
  have htrace : WordTrace (prefixWord ++ tailWord_1373917) baseStart_1373917 baseEnd_1373917 := by
    simpa [prefixWord, tailWord_1373917, baseEnd_1373917] using wordTrace_append hprefix tailTrace_1373917
  have hstable : (prefixWord ++ tailWord_1373917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373917).length < 2 ^ (prefixWord ++ tailWord_1373917).sum := by decide
  have hdescent : baseEnd_1373917 < baseStart_1373917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373953 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1373953 : Nat := 118140960795 + 1373953 * 2 ^ 59
def prefixEnd_1373953 : Nat := 4983230072969 + 3 ^ 40 * 1373953 * 2
def baseEnd_1373953 : Nat := 705498285686968136268811

theorem tailTrace_1373953 : CollatzResearch.WordTrace tailWord_1373953 prefixEnd_1373953 705498285686968136268811 := by
  unfold tailWord_1373953
  simp only [CollatzResearch.WordTrace]
  refine ⟨50112182791410408335870513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33408121860940272223913675 50112182791410408335870513)
  ·
    refine ⟨37584137093557806251902885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50112182791410408335870513 37584137093557806251902885)
    ·
      refine ⟨7047025705042088672231791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37584137093557806251902885 7047025705042088672231791)
      ·
        refine ⟨10570538557563133008347687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7047025705042088672231791 10570538557563133008347687)
        ·
          refine ⟨15855807836344699512521531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10570538557563133008347687 15855807836344699512521531)
          ·
            refine ⟨23783711754517049268782297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15855807836344699512521531 23783711754517049268782297)
            ·
              refine ⟨17837783815887786951586723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23783711754517049268782297 17837783815887786951586723)
              ·
                refine ⟨26756675723831680427380085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17837783815887786951586723 26756675723831680427380085)
                ·
                  refine ⟨2508438349109220040066883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26756675723831680427380085 2508438349109220040066883)
                  ·
                    refine ⟨3762657523663830060100325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2508438349109220040066883 3762657523663830060100325)
                    ·
                      refine ⟨705498285686968136268811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3762657523663830060100325 705498285686968136268811)
                      ·
                        rfl

theorem cell23_1373953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1373953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373953 prefixEnd_1373953 := by exact prefixLift 1373953
  have htrace : WordTrace (prefixWord ++ tailWord_1373953) baseStart_1373953 baseEnd_1373953 := by
    simpa [prefixWord, tailWord_1373953, baseEnd_1373953] using wordTrace_append hprefix tailTrace_1373953
  have hstable : (prefixWord ++ tailWord_1373953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373953).length < 2 ^ (prefixWord ++ tailWord_1373953).sum := by decide
  have hdescent : baseEnd_1373953 < baseStart_1373953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373963 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 1, 6]
def baseStart_1373963 : Nat := 118140960795 + 1373963 * 2 ^ 59
def prefixEnd_1373963 : Nat := 4983230072969 + 3 ^ 40 * 1373963 * 2
def baseEnd_1373963 : Nat := 235167806831171032381255

theorem tailTrace_1373963 : CollatzResearch.WordTrace tailWord_1373963 prefixEnd_1373963 235167806831171032381255 := by
  unfold tailWord_1373963
  simp only [CollatzResearch.WordTrace]
  refine ⟨50112547521374180043734543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33408365014249453362489695 50112547521374180043734543)
  ·
    refine ⟨75168821282061270065601815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50112547521374180043734543 75168821282061270065601815)
    ·
      refine ⟨112753231923091905098402723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75168821282061270065601815 112753231923091905098402723)
      ·
        refine ⟨169129847884637857647604085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112753231923091905098402723 169129847884637857647604085)
        ·
          refine ⟨15855923239184799154462883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169129847884637857647604085 15855923239184799154462883)
          ·
            refine ⟨23783884858777198731694325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15855923239184799154462883 23783884858777198731694325)
            ·
              refine ⟨2229739205510362381096343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23783884858777198731694325 2229739205510362381096343)
              ·
                refine ⟨3344608808265543571644515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229739205510362381096343 3344608808265543571644515)
                ·
                  refine ⟨5016913212398315357466773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344608808265543571644515 5016913212398315357466773)
                  ·
                    refine ⟨235167806831171032381255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5016913212398315357466773 235167806831171032381255)
                    ·
                      rfl

theorem cell23_1373963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 6].length) (baseStart_1373963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373963 prefixEnd_1373963 := by exact prefixLift 1373963
  have htrace : WordTrace (prefixWord ++ tailWord_1373963) baseStart_1373963 baseEnd_1373963 := by
    simpa [prefixWord, tailWord_1373963, baseEnd_1373963] using wordTrace_append hprefix tailTrace_1373963
  have hstable : (prefixWord ++ tailWord_1373963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373963).length < 2 ^ (prefixWord ++ tailWord_1373963).sum := by decide
  have hdescent : baseEnd_1373963 < baseStart_1373963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373983 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1373983 : Nat := 118140960795 + 1373983 * 2 ^ 59
def prefixEnd_1373983 : Nat := 4983230072969 + 3 ^ 40 * 1373983 * 2
def baseEnd_1373983 : Nat := 705513690106603018893673

theorem tailTrace_1373983 : CollatzResearch.WordTrace tailWord_1373983 prefixEnd_1373983 705513690106603018893673 := by
  unfold tailWord_1373983
  simp only [CollatzResearch.WordTrace]
  refine ⟨50113276981301723459462603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33408851320867815639641735 50113276981301723459462603)
  ·
    refine ⟨75169915471952585189193905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50113276981301723459462603 75169915471952585189193905)
    ·
      refine ⟨56377436603964438891895429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75169915471952585189193905 56377436603964438891895429)
      ·
        refine ⟨10570769363243332292230393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56377436603964438891895429 10570769363243332292230393)
        ·
          refine ⟨7928077022432499219172795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10570769363243332292230393 7928077022432499219172795)
          ·
            refine ⟨11892115533648748828759193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7928077022432499219172795 11892115533648748828759193)
            ·
              refine ⟨8919086650236561621569395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11892115533648748828759193 8919086650236561621569395)
              ·
                refine ⟨13378629975354842432354093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919086650236561621569395 13378629975354842432354093)
                ·
                  refine ⟨5016986240758065912132785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13378629975354842432354093 5016986240758065912132785)
                  ·
                    refine ⟨3762739680568549434099589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5016986240758065912132785 3762739680568549434099589)
                    ·
                      refine ⟨705513690106603018893673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3762739680568549434099589 705513690106603018893673)
                      ·
                        rfl

theorem cell23_1373983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1373983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373983 prefixEnd_1373983 := by exact prefixLift 1373983
  have htrace : WordTrace (prefixWord ++ tailWord_1373983) baseStart_1373983 baseEnd_1373983 := by
    simpa [prefixWord, tailWord_1373983, baseEnd_1373983] using wordTrace_append hprefix tailTrace_1373983
  have hstable : (prefixWord ++ tailWord_1373983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373983).length < 2 ^ (prefixWord ++ tailWord_1373983).sum := by decide
  have hdescent : baseEnd_1373983 < baseStart_1373983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373998 : List Nat := [4, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1373998 : Nat := 118140960795 + 1373998 * 2 ^ 59
def prefixEnd_1373998 : Nat := 4983230072969 + 3 ^ 40 * 1373998 * 2
def baseEnd_1373998 : Nat := 705521392316420460206105

theorem tailTrace_1373998 : CollatzResearch.WordTrace tailWord_1373998 prefixEnd_1373998 705521392316420460206105 := by
  unfold tailWord_1373998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264228009530922627657331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33409216050831587347505765 6264228009530922627657331)
  ·
    refine ⟨9396342014296383941485997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6264228009530922627657331 9396342014296383941485997)
    ·
      refine ⟨3523628255361143978057249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9396342014296383941485997 3523628255361143978057249)
      ·
        refine ⟨2642721191520857983542937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3523628255361143978057249 2642721191520857983542937)
        ·
          refine ⟨1982040893640643487657203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2642721191520857983542937 1982040893640643487657203)
          ·
            refine ⟨2973061340460965231485805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982040893640643487657203 2973061340460965231485805)
            ·
              refine ⟨1114898002672861961807177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2973061340460965231485805 1114898002672861961807177)
              ·
                refine ⟨836173502004646471355383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114898002672861961807177 836173502004646471355383)
                ·
                  refine ⟨1254260253006969707033075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836173502004646471355383 1254260253006969707033075)
                  ·
                    refine ⟨1881390379510454560549613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1254260253006969707033075 1881390379510454560549613)
                    ·
                      refine ⟨705521392316420460206105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1881390379510454560549613 705521392316420460206105)
                      ·
                        rfl

theorem cell23_1373998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1373998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1373998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1373998 prefixEnd_1373998 := by exact prefixLift 1373998
  have htrace : WordTrace (prefixWord ++ tailWord_1373998) baseStart_1373998 baseEnd_1373998 := by
    simpa [prefixWord, tailWord_1373998, baseEnd_1373998] using wordTrace_append hprefix tailTrace_1373998
  have hstable : (prefixWord ++ tailWord_1373998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373998).length < 2 ^ (prefixWord ++ tailWord_1373998).sum := by decide
  have hdescent : baseEnd_1373998 < baseStart_1373998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374014 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1374014 : Nat := 118140960795 + 1374014 * 2 ^ 59
def prefixEnd_1374014 : Nat := 4983230072969 + 3 ^ 40 * 1374014 * 2
def baseEnd_1374014 : Nat := 235176536002297465868677

theorem tailTrace_1374014 : CollatzResearch.WordTrace tailWord_1374014 prefixEnd_1374014 235176536002297465868677 := by
  unfold tailWord_1374014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264300955523676969230137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33409605096126277169227397 6264300955523676969230137)
  ·
    refine ⟨4698225716642757726922603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6264300955523676969230137 4698225716642757726922603)
    ·
      refine ⟨7047338574964136590383905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4698225716642757726922603 7047338574964136590383905)
      ·
        refine ⟨5285503931223102442787929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7047338574964136590383905 5285503931223102442787929)
        ·
          refine ⟨3964127948417326832090947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5285503931223102442787929 3964127948417326832090947)
          ·
            refine ⟨5946191922625990248136421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964127948417326832090947 5946191922625990248136421)
            ·
              refine ⟨1114910985492373171525579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5946191922625990248136421 1114910985492373171525579)
              ·
                refine ⟨1672366478238559757288369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114910985492373171525579 1672366478238559757288369)
                ·
                  refine ⟨1254274858678919817966277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1672366478238559757288369 1254274858678919817966277)
                  ·
                    refine ⟨235176536002297465868677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254274858678919817966277 235176536002297465868677)
                    ·
                      rfl

theorem cell23_1374014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1374014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374014 prefixEnd_1374014 := by exact prefixLift 1374014
  have htrace : WordTrace (prefixWord ++ tailWord_1374014) baseStart_1374014 baseEnd_1374014 := by
    simpa [prefixWord, tailWord_1374014, baseEnd_1374014] using wordTrace_append hprefix tailTrace_1374014
  have hstable : (prefixWord ++ tailWord_1374014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374014).length < 2 ^ (prefixWord ++ tailWord_1374014).sum := by decide
  have hdescent : baseEnd_1374014 < baseStart_1374014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374053 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_1374053 : Nat := 118140960795 + 1374053 * 2 ^ 59
def prefixEnd_1374053 : Nat := 4983230072969 + 3 ^ 40 * 1374053 * 2
def baseEnd_1374053 : Nat := 235183211250805915006117

theorem tailTrace_1374053 : CollatzResearch.WordTrace tailWord_1374053 prefixEnd_1374053 235183211250805915006117 := by
  unfold tailWord_1374053
  simp only [CollatzResearch.WordTrace]
  refine ⟨50115830091048125414510813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33410553394032083609673875 50115830091048125414510813)
  ·
    refine ⟨18793436284143047030441555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50115830091048125414510813 18793436284143047030441555)
    ·
      refine ⟨28190154426214570545662333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18793436284143047030441555 28190154426214570545662333)
      ·
        refine ⟨10571307909830463954623375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28190154426214570545662333 10571307909830463954623375)
        ·
          refine ⟨15856961864745695931935063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10571307909830463954623375 15856961864745695931935063)
          ·
            refine ⟨23785442797118543897902595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15856961864745695931935063 23785442797118543897902595)
            ·
              refine ⟨35678164195677815846853893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23785442797118543897902595 35678164195677815846853893)
              ·
                refine ⟨6689655786689590471285105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35678164195677815846853893 6689655786689590471285105)
                ·
                  refine ⟨5017241840017192853463829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6689655786689590471285105 5017241840017192853463829)
                  ·
                    refine ⟨235183211250805915006117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5017241840017192853463829 235183211250805915006117)
                    ·
                      rfl

theorem cell23_1374053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_1374053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374053 prefixEnd_1374053 := by exact prefixLift 1374053
  have htrace : WordTrace (prefixWord ++ tailWord_1374053) baseStart_1374053 baseEnd_1374053 := by
    simpa [prefixWord, tailWord_1374053, baseEnd_1374053] using wordTrace_append hprefix tailTrace_1374053
  have hstable : (prefixWord ++ tailWord_1374053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374053).length < 2 ^ (prefixWord ++ tailWord_1374053).sum := by decide
  have hdescent : baseEnd_1374053 < baseStart_1374053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374077 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_1374077 : Nat := 118140960795 + 1374077 * 2 ^ 59
def prefixEnd_1374077 : Nat := 4983230072969 + 3 ^ 40 * 1374077 * 2
def baseEnd_1374077 : Nat := 705561957288125651118241

theorem tailTrace_1374077 : CollatzResearch.WordTrace tailWord_1374077 prefixEnd_1374077 705561957288125651118241 := by
  unfold tailWord_1374077
  simp only [CollatzResearch.WordTrace]
  refine ⟨50116705442961177513384485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33411136961974118342256323 50116705442961177513384485)
  ·
    refine ⟨9396882270555220783759591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50116705442961177513384485 9396882270555220783759591)
    ·
      refine ⟨14095323405832831175639387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396882270555220783759591 14095323405832831175639387)
      ·
        refine ⟨21142985108749246763459081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14095323405832831175639387 21142985108749246763459081)
        ·
          refine ⟨15857238831561935072594311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21142985108749246763459081 15857238831561935072594311)
          ·
            refine ⟨23785858247342902608891467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15857238831561935072594311 23785858247342902608891467)
            ·
              refine ⟨35678787371014353913337201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23785858247342902608891467 35678787371014353913337201)
              ·
                refine ⟨26759090528260765435002901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35678787371014353913337201 26759090528260765435002901)
                ·
                  refine ⟨1254332368512223379765761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26759090528260765435002901 1254332368512223379765761)
                  ·
                    refine ⟨940749276384167534824321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1254332368512223379765761 940749276384167534824321)
                    ·
                      refine ⟨705561957288125651118241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940749276384167534824321 705561957288125651118241)
                      ·
                        rfl

theorem cell23_1374077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_1374077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374077 prefixEnd_1374077 := by exact prefixLift 1374077
  have htrace : WordTrace (prefixWord ++ tailWord_1374077) baseStart_1374077 baseEnd_1374077 := by
    simpa [prefixWord, tailWord_1374077, baseEnd_1374077] using wordTrace_append hprefix tailTrace_1374077
  have hstable : (prefixWord ++ tailWord_1374077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374077).length < 2 ^ (prefixWord ++ tailWord_1374077).sum := by decide
  have hdescent : baseEnd_1374077 < baseStart_1374077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374083 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 9]
def baseStart_1374083 : Nat := 118140960795 + 1374083 * 2 ^ 59
def prefixEnd_1374083 : Nat := 4983230072969 + 3 ^ 40 * 1374083 * 2
def baseEnd_1374083 : Nat := 78396115352450291960357

theorem tailTrace_1374083 : CollatzResearch.WordTrace tailWord_1374083 prefixEnd_1374083 78396115352450291960357 := by
  unfold tailWord_1374083
  simp only [CollatzResearch.WordTrace]
  refine ⟨50116924280939440538102903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33411282853959627025401935 50116924280939440538102903)
  ·
    refine ⟨75175386421409160807154355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50116924280939440538102903 75175386421409160807154355)
    ·
      refine ⟨112763079632113741210731533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75175386421409160807154355 112763079632113741210731533)
      ·
        refine ⟨42286154862042652954024325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112763079632113741210731533 42286154862042652954024325)
        ·
          refine ⟨7928654036632997428879561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42286154862042652954024325 7928654036632997428879561)
          ·
            refine ⟨5946490527474748071659671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7928654036632997428879561 5946490527474748071659671)
            ·
              refine ⟨8919735791212122107489507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946490527474748071659671 8919735791212122107489507)
              ·
                refine ⟨13379603686818183161234261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919735791212122107489507 13379603686818183161234261)
                ·
                  refine ⟨78396115352450291960357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13379603686818183161234261 78396115352450291960357)
                  ·
                    rfl

theorem cell23_1374083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 9].length) (baseStart_1374083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374083 prefixEnd_1374083 := by exact prefixLift 1374083
  have htrace : WordTrace (prefixWord ++ tailWord_1374083) baseStart_1374083 baseEnd_1374083 := by
    simpa [prefixWord, tailWord_1374083, baseEnd_1374083] using wordTrace_append hprefix tailTrace_1374083
  have hstable : (prefixWord ++ tailWord_1374083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374083).length < 2 ^ (prefixWord ++ tailWord_1374083).sum := by decide
  have hdescent : baseEnd_1374083 < baseStart_1374083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374098 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_1374098 : Nat := 118140960795 + 1374098 * 2 ^ 59
def prefixEnd_1374098 : Nat := 4983230072969 + 3 ^ 40 * 1374098 * 2
def baseEnd_1374098 : Nat := 705572740381870068955645

theorem tailTrace_1374098 : CollatzResearch.WordTrace tailWord_1374098 prefixEnd_1374098 705572740381870068955645 := by
  unfold tailWord_1374098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12529367843971274524974737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33411647583923398733265965 12529367843971274524974737)
  ·
    refine ⟨9397025882978455893731053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12529367843971274524974737 9397025882978455893731053)
    ·
      refine ⟨3523884706116920960149145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9397025882978455893731053 3523884706116920960149145)
      ·
        refine ⟨2642913529587690720111859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3523884706116920960149145 2642913529587690720111859)
        ·
          refine ⟨3964370294381536080167789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2642913529587690720111859 3964370294381536080167789)
          ·
            refine ⟨1486638860393076030062921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3964370294381536080167789 1486638860393076030062921)
            ·
              refine ⟨1114979145294807022547191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486638860393076030062921 1114979145294807022547191)
              ·
                refine ⟨1672468717942210533820787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114979145294807022547191 1672468717942210533820787)
                ·
                  refine ⟨2508703076913315800731181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672468717942210533820787 2508703076913315800731181)
                  ·
                    refine ⟨940763653842493425274193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2508703076913315800731181 940763653842493425274193)
                    ·
                      refine ⟨705572740381870068955645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940763653842493425274193 705572740381870068955645)
                      ·
                        rfl

theorem cell23_1374098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_1374098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374098 prefixEnd_1374098 := by exact prefixLift 1374098
  have htrace : WordTrace (prefixWord ++ tailWord_1374098) baseStart_1374098 baseEnd_1374098 := by
    simpa [prefixWord, tailWord_1374098, baseEnd_1374098] using wordTrace_append hprefix tailTrace_1374098
  have hstable : (prefixWord ++ tailWord_1374098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374098).length < 2 ^ (prefixWord ++ tailWord_1374098).sum := by decide
  have hdescent : baseEnd_1374098 < baseStart_1374098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374143 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 2, 8]
def baseStart_1374143 : Nat := 118140960795 + 1374143 * 2 ^ 59
def prefixEnd_1374143 : Nat := 4983230072969 + 3 ^ 40 * 1374143 * 2
def baseEnd_1374143 : Nat := 235198615670440797630979

theorem tailTrace_1374143 : CollatzResearch.WordTrace tailWord_1374143 prefixEnd_1374143 235198615670440797630979 := by
  unfold tailWord_1374143
  simp only [CollatzResearch.WordTrace]
  refine ⟨50119112660722070785287083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33412741773814713856858055 50119112660722070785287083)
  ·
    refine ⟨75178668991083106177930625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50119112660722070785287083 75178668991083106177930625)
    ·
      refine ⟨56384001743312329633447969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75178668991083106177930625 56384001743312329633447969)
      ·
        refine ⟨42288001307484247225085977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56384001743312329633447969 42288001307484247225085977)
        ·
          refine ⟨31716000980613185418814483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42288001307484247225085977 31716000980613185418814483)
          ·
            refine ⟨47574001470919778128221725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31716000980613185418814483 47574001470919778128221725)
            ·
              refine ⟨17840250551594916798083147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47574001470919778128221725 17840250551594916798083147)
              ·
                refine ⟨26760375827392375197124721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17840250551594916798083147 26760375827392375197124721)
                ·
                  refine ⟨20070281870544281397843541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26760375827392375197124721 20070281870544281397843541)
                  ·
                    refine ⟨235198615670440797630979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20070281870544281397843541 235198615670440797630979)
                    ·
                      rfl

theorem cell23_1374143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_1374143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374143 prefixEnd_1374143 := by exact prefixLift 1374143
  have htrace : WordTrace (prefixWord ++ tailWord_1374143) baseStart_1374143 baseEnd_1374143 := by
    simpa [prefixWord, tailWord_1374143, baseEnd_1374143] using wordTrace_append hprefix tailTrace_1374143
  have hstable : (prefixWord ++ tailWord_1374143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374143).length < 2 ^ (prefixWord ++ tailWord_1374143).sum := by decide
  have hdescent : baseEnd_1374143 < baseStart_1374143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374160 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 5, 4]
def baseStart_1374160 : Nat := 118140960795 + 1374160 * 2 ^ 59
def prefixEnd_1374160 : Nat := 4983230072969 + 3 ^ 40 * 1374160 * 2
def baseEnd_1374160 : Nat := 235201525394149608793453

theorem tailTrace_1374160 : CollatzResearch.WordTrace tailWord_1374160 prefixEnd_1374160 235201525394149608793453 := by
  unfold tailWord_1374160
  simp only [CollatzResearch.WordTrace]
  refine ⟨25059866350830241344327967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33413155134440321792437289 25059866350830241344327967)
  ·
    refine ⟨37589799526245362016491951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25059866350830241344327967 37589799526245362016491951)
    ·
      refine ⟨56384699289368043024737927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37589799526245362016491951 56384699289368043024737927)
      ·
        refine ⟨84577048934052064537106891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56384699289368043024737927 84577048934052064537106891)
        ·
          refine ⟨126865573401078096805660337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84577048934052064537106891 126865573401078096805660337)
          ·
            refine ⟨95149180050808572604245253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126865573401078096805660337 95149180050808572604245253)
            ·
              refine ⟨17840471259526607363295985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95149180050808572604245253 17840471259526607363295985)
              ·
                refine ⟨13380353444644955522471989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17840471259526607363295985 13380353444644955522471989)
                ·
                  refine ⟨1254408135435464580231749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13380353444644955522471989 1254408135435464580231749)
                  ·
                    refine ⟨235201525394149608793453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254408135435464580231749 235201525394149608793453)
                    ·
                      rfl

theorem cell23_1374160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 4].length) (baseStart_1374160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374160 prefixEnd_1374160 := by exact prefixLift 1374160
  have htrace : WordTrace (prefixWord ++ tailWord_1374160) baseStart_1374160 baseEnd_1374160 := by
    simpa [prefixWord, tailWord_1374160, baseEnd_1374160] using wordTrace_append hprefix tailTrace_1374160
  have hstable : (prefixWord ++ tailWord_1374160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374160).length < 2 ^ (prefixWord ++ tailWord_1374160).sum := by decide
  have hdescent : baseEnd_1374160 < baseStart_1374160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374177 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 3, 4]
def baseStart_1374177 : Nat := 118140960795 + 1374177 * 2 ^ 59
def prefixEnd_1374177 : Nat := 4983230072969 + 3 ^ 40 * 1374177 * 2
def baseEnd_1374177 : Nat := 235204435117858419955927

theorem tailTrace_1374177 : CollatzResearch.WordTrace tailWord_1374177 prefixEnd_1374177 235204435117858419955927 := by
  unfold tailWord_1374177
  simp only [CollatzResearch.WordTrace]
  refine ⟨50120352742598894592024785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33413568495065929728016523 50120352742598894592024785)
  ·
    refine ⟨37590264556949170944018589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50120352742598894592024785 37590264556949170944018589)
    ·
      refine ⟨14096349208855939104006971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37590264556949170944018589 14096349208855939104006971)
      ·
        refine ⟨21144523813283908656010457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14096349208855939104006971 21144523813283908656010457)
        ·
          refine ⟨15858392859962931492007843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21144523813283908656010457 15858392859962931492007843)
          ·
            refine ⟨23787589289944397238011765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15858392859962931492007843 23787589289944397238011765)
            ·
              refine ⟨2230086495932287241063603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23787589289944397238011765 2230086495932287241063603)
              ·
                refine ⟨3345129743898430861595405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230086495932287241063603 3345129743898430861595405)
                ·
                  refine ⟨1254423653961911573098277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3345129743898430861595405 1254423653961911573098277)
                  ·
                    refine ⟨235204435117858419955927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254423653961911573098277 235204435117858419955927)
                    ·
                      rfl

theorem cell23_1374177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_1374177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374177 prefixEnd_1374177 := by exact prefixLift 1374177
  have htrace : WordTrace (prefixWord ++ tailWord_1374177) baseStart_1374177 baseEnd_1374177 := by
    simpa [prefixWord, tailWord_1374177, baseEnd_1374177] using wordTrace_append hprefix tailTrace_1374177
  have hstable : (prefixWord ++ tailWord_1374177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374177).length < 2 ^ (prefixWord ++ tailWord_1374177).sum := by decide
  have hdescent : baseEnd_1374177 < baseStart_1374177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374200 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_1374200 : Nat := 118140960795 + 1374200 * 2 ^ 59
def prefixEnd_1374200 : Nat := 4983230072969 + 3 ^ 40 * 1374200 * 2
def baseEnd_1374200 : Nat := 705625115408628669880175

theorem tailTrace_1374200 : CollatzResearch.WordTrace tailWord_1374200 prefixEnd_1374200 705625115408628669880175 := by
  unfold tailWord_1374200
  simp only [CollatzResearch.WordTrace]
  refine ⟨25060595810757784760056027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33414127747677046346741369 25060595810757784760056027)
  ·
    refine ⟨37590893716136677140084041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25060595810757784760056027 37590893716136677140084041)
    ·
      refine ⟨28193170287102507855063031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37590893716136677140084041 28193170287102507855063031)
      ·
        refine ⟨42289755430653761782594547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28193170287102507855063031 42289755430653761782594547)
        ·
          refine ⟨63434633145980642673891821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42289755430653761782594547 63434633145980642673891821)
          ·
            refine ⟨23787987429742741002709433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63434633145980642673891821 23787987429742741002709433)
            ·
              refine ⟨17840990572307055752032075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23787987429742741002709433 17840990572307055752032075)
              ·
                refine ⟨26761485858460583628048113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17840990572307055752032075 26761485858460583628048113)
                ·
                  refine ⟨20071114393845437721036085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26761485858460583628048113 20071114393845437721036085)
                  ·
                    refine ⟨1881666974423009786347133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20071114393845437721036085 1881666974423009786347133)
                    ·
                      refine ⟨705625115408628669880175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1881666974423009786347133 705625115408628669880175)
                      ·
                        rfl

theorem cell23_1374200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_1374200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374200 prefixEnd_1374200 := by exact prefixLift 1374200
  have htrace : WordTrace (prefixWord ++ tailWord_1374200) baseStart_1374200 baseEnd_1374200 := by
    simpa [prefixWord, tailWord_1374200, baseEnd_1374200] using wordTrace_append hprefix tailTrace_1374200
  have hstable : (prefixWord ++ tailWord_1374200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374200).length < 2 ^ (prefixWord ++ tailWord_1374200).sum := by decide
  have hdescent : baseEnd_1374200 < baseStart_1374200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374237 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1374237 : Nat := 118140960795 + 1374237 * 2 ^ 59
def prefixEnd_1374237 : Nat := 4983230072969 + 3 ^ 40 * 1374237 * 2
def baseEnd_1374237 : Nat := 235214704730948341705835

theorem tailTrace_1374237 : CollatzResearch.WordTrace tailWord_1374237 prefixEnd_1374237 235214704730948341705835 := by
  unfold tailWord_1374237
  simp only [CollatzResearch.WordTrace]
  refine ⟨50122541122381524839208965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33415027414921016559472643 50122541122381524839208965)
  ·
    refine ⟨9397976460446535907351681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50122541122381524839208965 9397976460446535907351681)
    ·
      refine ⟨7048482345334901930513761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9397976460446535907351681 7048482345334901930513761)
      ·
        refine ⟨5286361759001176447885321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7048482345334901930513761 5286361759001176447885321)
        ·
          refine ⟨3964771319250882335913991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286361759001176447885321 3964771319250882335913991)
          ·
            refine ⟨5947156978876323503870987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964771319250882335913991 5947156978876323503870987)
            ·
              refine ⟨8920735468314485255806481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5947156978876323503870987 8920735468314485255806481)
              ·
                refine ⟨6690551601235863941854861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8920735468314485255806481 6690551601235863941854861)
                ·
                  refine ⟨2508956850463448978195573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6690551601235863941854861 2508956850463448978195573)
                  ·
                    refine ⟨235214704730948341705835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2508956850463448978195573 235214704730948341705835)
                    ·
                      rfl

theorem cell23_1374237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1374237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374237 prefixEnd_1374237 := by exact prefixLift 1374237
  have htrace : WordTrace (prefixWord ++ tailWord_1374237) baseStart_1374237 baseEnd_1374237 := by
    simpa [prefixWord, tailWord_1374237, baseEnd_1374237] using wordTrace_append hprefix tailTrace_1374237
  have hstable : (prefixWord ++ tailWord_1374237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374237).length < 2 ^ (prefixWord ++ tailWord_1374237).sum := by decide
  have hdescent : baseEnd_1374237 < baseStart_1374237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374257 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1374257 : Nat := 118140960795 + 1374257 * 2 ^ 59
def prefixEnd_1374257 : Nat := 4983230072969 + 3 ^ 40 * 1374257 * 2
def baseEnd_1374257 : Nat := 705654383805934946867413

theorem tailTrace_1374257 : CollatzResearch.WordTrace tailWord_1374257 prefixEnd_1374257 705654383805934946867413 := by
  unfold tailWord_1374257
  simp only [CollatzResearch.WordTrace]
  refine ⟨50123270582309068254937025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33415513721539378836624683 50123270582309068254937025)
  ·
    refine ⟨37592452936731801191202769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50123270582309068254937025 37592452936731801191202769)
    ·
      refine ⟨28194339702548850893402077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37592452936731801191202769 28194339702548850893402077)
      ·
        refine ⟨10572877388455819085025779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28194339702548850893402077 10572877388455819085025779)
        ·
          refine ⟨15859316082683728627538669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10572877388455819085025779 15859316082683728627538669)
          ·
            refine ⟨5947243531006398235327001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15859316082683728627538669 5947243531006398235327001)
            ·
              refine ⟨4460432648254798676495251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5947243531006398235327001 4460432648254798676495251)
              ·
                refine ⟨6690648972382198014742877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460432648254798676495251 6690648972382198014742877)
                ·
                  refine ⟨2508993364643324255528579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6690648972382198014742877 2508993364643324255528579)
                  ·
                    refine ⟨3763490046964986383292869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2508993364643324255528579 3763490046964986383292869)
                    ·
                      refine ⟨705654383805934946867413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3763490046964986383292869 705654383805934946867413)
                      ·
                        rfl

theorem cell23_1374257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1374257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374257 prefixEnd_1374257 := by exact prefixLift 1374257
  have htrace : WordTrace (prefixWord ++ tailWord_1374257) baseStart_1374257 baseEnd_1374257 := by
    simpa [prefixWord, tailWord_1374257, baseEnd_1374257] using wordTrace_append hprefix tailTrace_1374257
  have hstable : (prefixWord ++ tailWord_1374257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374257).length < 2 ^ (prefixWord ++ tailWord_1374257).sum := by decide
  have hdescent : baseEnd_1374257 < baseStart_1374257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374284 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_1374284 : Nat := 118140960795 + 1374284 * 2 ^ 59
def prefixEnd_1374284 : Nat := 4983230072969 + 3 ^ 40 * 1374284 * 2
def baseEnd_1374284 : Nat := 235222749261202113743263

theorem tailTrace_1374284 : CollatzResearch.WordTrace tailWord_1374284 prefixEnd_1374284 235222749261202113743263 := by
  unfold tailWord_1374284
  simp only [CollatzResearch.WordTrace]
  refine ⟨25062127676605625933084953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33416170235474167910779937 25062127676605625933084953)
  ·
    refine ⟨18796595757454219449813715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25062127676605625933084953 18796595757454219449813715)
    ·
      refine ⟨28194893636181329174720573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18796595757454219449813715 28194893636181329174720573)
      ·
        refine ⟨10573085113567998440520215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28194893636181329174720573 10573085113567998440520215)
        ·
          refine ⟨15859627670351997660780323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10573085113567998440520215 15859627670351997660780323)
          ·
            refine ⟨23789441505527996491170485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15859627670351997660780323 23789441505527996491170485)
            ·
              refine ⟨2230260141143249671047233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23789441505527996491170485 2230260141143249671047233)
              ·
                refine ⟨1672695105857437253285425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2230260141143249671047233 1672695105857437253285425)
                ·
                  refine ⟨1254521329393077939964069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1672695105857437253285425 1254521329393077939964069)
                  ·
                    refine ⟨235222749261202113743263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254521329393077939964069 235222749261202113743263)
                    ·
                      rfl

theorem cell23_1374284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_1374284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374284 prefixEnd_1374284 := by exact prefixLift 1374284
  have htrace : WordTrace (prefixWord ++ tailWord_1374284) baseStart_1374284 baseEnd_1374284 := by
    simpa [prefixWord, tailWord_1374284, baseEnd_1374284] using wordTrace_append hprefix tailTrace_1374284
  have hstable : (prefixWord ++ tailWord_1374284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374284).length < 2 ^ (prefixWord ++ tailWord_1374284).sum := by decide
  have hdescent : baseEnd_1374284 < baseStart_1374284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374301 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1374301 : Nat := 118140960795 + 1374301 * 2 ^ 59
def prefixEnd_1374301 : Nat := 4983230072969 + 3 ^ 40 * 1374301 * 2
def baseEnd_1374301 : Nat := 235225658984910924905737

theorem tailTrace_1374301 : CollatzResearch.WordTrace tailWord_1374301 prefixEnd_1374301 235225658984910924905737 := by
  unfold tailWord_1374301
  simp only [CollatzResearch.WordTrace]
  refine ⟨50124875394149663769538757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33416583596099775846359171 50124875394149663769538757)
  ·
    refine ⟨9398414136403061956788517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50124875394149663769538757 9398414136403061956788517)
    ·
      refine ⟨1762202650575574116897847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9398414136403061956788517 1762202650575574116897847)
      ·
        refine ⟨2643303975863361175346771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762202650575574116897847 2643303975863361175346771)
        ·
          refine ⟨3964955963795041763020157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643303975863361175346771 3964955963795041763020157)
          ·
            refine ⟨1486858486423140661132559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3964955963795041763020157 1486858486423140661132559)
            ·
              refine ⟨2230287729634710991698839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486858486423140661132559 2230287729634710991698839)
              ·
                refine ⟨3345431594452066487548259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230287729634710991698839 3345431594452066487548259)
                ·
                  refine ⟨5018147391678099731322389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345431594452066487548259 5018147391678099731322389)
                  ·
                    refine ⟨235225658984910924905737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5018147391678099731322389 235225658984910924905737)
                    ·
                      rfl

theorem cell23_1374301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1374301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374301 prefixEnd_1374301 := by exact prefixLift 1374301
  have htrace : WordTrace (prefixWord ++ tailWord_1374301) baseStart_1374301 baseEnd_1374301 := by
    simpa [prefixWord, tailWord_1374301, baseEnd_1374301] using wordTrace_append hprefix tailTrace_1374301
  have hstable : (prefixWord ++ tailWord_1374301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374301).length < 2 ^ (prefixWord ++ tailWord_1374301).sum := by decide
  have hdescent : baseEnd_1374301 < baseStart_1374301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374304 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 4]
def baseStart_1374304 : Nat := 118140960795 + 1374304 * 2 ^ 59
def prefixEnd_1374304 : Nat := 4983230072969 + 3 ^ 40 * 1374304 * 2
def baseEnd_1374304 : Nat := 705678517396696262979697

theorem tailTrace_1374304 : CollatzResearch.WordTrace tailWord_1374304 prefixEnd_1374304 705678517396696262979697 := by
  unfold tailWord_1374304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25062492406569397640948983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33416656542092530187931977 25062492406569397640948983)
  ·
    refine ⟨37593738609854096461423475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25062492406569397640948983 37593738609854096461423475)
    ·
      refine ⟨56390607914781144692135213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37593738609854096461423475 56390607914781144692135213)
      ·
        refine ⟨21146477968042929259550705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56390607914781144692135213 21146477968042929259550705)
        ·
          refine ⟨15859858476032196944663029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21146477968042929259550705 15859858476032196944663029)
          ·
            refine ⟨1486861732128018463562159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15859858476032196944663029 1486861732128018463562159)
            ·
              refine ⟨2230292598192027695343239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486861732128018463562159 2230292598192027695343239)
              ·
                refine ⟨3345438897288041543014859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230292598192027695343239 3345438897288041543014859)
                ·
                  refine ⟨5018158345932062314522289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345438897288041543014859 5018158345932062314522289)
                  ·
                    refine ⟨3763618759449046735891717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5018158345932062314522289 3763618759449046735891717)
                    ·
                      refine ⟨705678517396696262979697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3763618759449046735891717 705678517396696262979697)
                      ·
                        rfl

theorem cell23_1374304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_1374304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374304 prefixEnd_1374304 := by exact prefixLift 1374304
  have htrace : WordTrace (prefixWord ++ tailWord_1374304) baseStart_1374304 baseEnd_1374304 := by
    simpa [prefixWord, tailWord_1374304, baseEnd_1374304] using wordTrace_append hprefix tailTrace_1374304
  have hstable : (prefixWord ++ tailWord_1374304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374304).length < 2 ^ (prefixWord ++ tailWord_1374304).sum := by decide
  have hdescent : baseEnd_1374304 < baseStart_1374304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374330 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_1374330 : Nat := 118140960795 + 1374330 * 2 ^ 59
def prefixEnd_1374330 : Nat := 4983230072969 + 3 ^ 40 * 1374330 * 2
def baseEnd_1374330 : Nat := 705691867893713161254577

theorem tailTrace_1374330 : CollatzResearch.WordTrace tailWord_1374330 prefixEnd_1374330 705691867893713161254577 := by
  unfold tailWord_1374330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12531483277761150430586111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33417288740696401148229629 12531483277761150430586111)
  ·
    refine ⟨18797224916641725645879167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12531483277761150430586111 18797224916641725645879167)
    ·
      refine ⟨28195837374962588468818751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18797224916641725645879167 28195837374962588468818751)
      ·
        refine ⟨42293756062443882703228127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28195837374962588468818751 42293756062443882703228127)
        ·
          refine ⟨63440634093665824054842191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42293756062443882703228127 63440634093665824054842191)
          ·
            refine ⟨95160951140498736082263287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63440634093665824054842191 95160951140498736082263287)
            ·
              refine ⟨142741426710748104123394931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95160951140498736082263287 142741426710748104123394931)
              ·
                refine ⟨214112140066122156185092397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142741426710748104123394931 214112140066122156185092397)
                ·
                  refine ⟨80292052524795808569409649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214112140066122156185092397 80292052524795808569409649)
                  ·
                    refine ⟨60219039393596856427057237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80292052524795808569409649 60219039393596856427057237)
                    ·
                      refine ⟨705691867893713161254577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 60219039393596856427057237 705691867893713161254577)
                      ·
                        rfl

theorem cell23_1374330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_1374330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374330 prefixEnd_1374330 := by exact prefixLift 1374330
  have htrace : WordTrace (prefixWord ++ tailWord_1374330) baseStart_1374330 baseEnd_1374330 := by
    simpa [prefixWord, tailWord_1374330, baseEnd_1374330] using wordTrace_append hprefix tailTrace_1374330
  have hstable : (prefixWord ++ tailWord_1374330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374330).length < 2 ^ (prefixWord ++ tailWord_1374330).sum := by decide
  have hdescent : baseEnd_1374330 < baseStart_1374330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374368 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 1, 3, 2]
def baseStart_1374368 : Nat := 118140960795 + 1374368 * 2 ^ 59
def prefixEnd_1374368 : Nat := 4983230072969 + 3 ^ 40 * 1374368 * 2
def baseEnd_1374368 : Nat := 705711380158584012579403

theorem tailTrace_1374368 : CollatzResearch.WordTrace tailWord_1374368 prefixEnd_1374368 705711380158584012579403 := by
  unfold tailWord_1374368
  simp only [CollatzResearch.WordTrace]
  refine ⟨25063659542453467106113879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33418212723271289474818505 25063659542453467106113879)
  ·
    refine ⟨37595489313680200659170819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25063659542453467106113879 37595489313680200659170819)
    ·
      refine ⟨56393233970520300988756229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37595489313680200659170819 56393233970520300988756229)
      ·
        refine ⟨10573731369472556435391793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56393233970520300988756229 10573731369472556435391793)
        ·
          refine ⟨7930298527104417326543845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10573731369472556435391793 7930298527104417326543845)
          ·
            refine ⟨1486930973832078248726971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7930298527104417326543845 1486930973832078248726971)
            ·
              refine ⟨2230396460748117373090457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486930973832078248726971 2230396460748117373090457)
              ·
                refine ⟨1672797345561088029817843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2230396460748117373090457 1672797345561088029817843)
                ·
                  refine ⟨2509196018341632044726765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672797345561088029817843 2509196018341632044726765)
                  ·
                    refine ⟨940948506878112016772537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509196018341632044726765 940948506878112016772537)
                    ·
                      refine ⟨705711380158584012579403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940948506878112016772537 705711380158584012579403)
                      ·
                        rfl

theorem cell23_1374368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_1374368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374368 prefixEnd_1374368 := by exact prefixLift 1374368
  have htrace : WordTrace (prefixWord ++ tailWord_1374368) baseStart_1374368 baseEnd_1374368 := by
    simpa [prefixWord, tailWord_1374368, baseEnd_1374368] using wordTrace_append hprefix tailTrace_1374368
  have hstable : (prefixWord ++ tailWord_1374368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374368).length < 2 ^ (prefixWord ++ tailWord_1374368).sum := by decide
  have hdescent : baseEnd_1374368 < baseStart_1374368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374381 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_1374381 : Nat := 118140960795 + 1374381 * 2 ^ 59
def prefixEnd_1374381 : Nat := 4983230072969 + 3 ^ 40 * 1374381 * 2
def baseEnd_1374381 : Nat := 705718055407092461716843

theorem tailTrace_1374381 : CollatzResearch.WordTrace tailWord_1374381 prefixEnd_1374381 705718055407092461716843 := by
  unfold tailWord_1374381
  simp only [CollatzResearch.WordTrace]
  refine ⟨50127793233859837432450997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33418528822573224954967331 50127793233859837432450997)
  ·
    refine ⟨4699480615674359759292281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50127793233859837432450997 4699480615674359759292281)
    ·
      refine ⟨3524610461755769819469211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4699480615674359759292281 3524610461755769819469211)
      ·
        refine ⟨5286915692633654729203817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524610461755769819469211 5286915692633654729203817)
        ·
          refine ⟨3965186769475241046902863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286915692633654729203817 3965186769475241046902863)
          ·
            refine ⟨5947780154212861570354295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965186769475241046902863 5947780154212861570354295)
            ·
              refine ⟨8921670231319292355531443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5947780154212861570354295 8921670231319292355531443)
              ·
                refine ⟨13382505346978938533297165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8921670231319292355531443 13382505346978938533297165)
                ·
                  refine ⟨5018439505117101949986437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13382505346978938533297165 5018439505117101949986437)
                  ·
                    refine ⟨940957407209456615622457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5018439505117101949986437 940957407209456615622457)
                    ·
                      refine ⟨705718055407092461716843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940957407209456615622457 705718055407092461716843)
                      ·
                        rfl

theorem cell23_1374381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_1374381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374381 prefixEnd_1374381 := by exact prefixLift 1374381
  have htrace : WordTrace (prefixWord ++ tailWord_1374381) baseStart_1374381 baseEnd_1374381 := by
    simpa [prefixWord, tailWord_1374381, baseEnd_1374381] using wordTrace_append hprefix tailTrace_1374381
  have hstable : (prefixWord ++ tailWord_1374381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374381).length < 2 ^ (prefixWord ++ tailWord_1374381).sum := by decide
  have hdescent : baseEnd_1374381 < baseStart_1374381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374385 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1374385 : Nat := 118140960795 + 1374385 * 2 ^ 59
def prefixEnd_1374385 : Nat := 4983230072969 + 3 ^ 40 * 1374385 * 2
def baseEnd_1374385 : Nat := 705720109329710446066825

theorem tailTrace_1374385 : CollatzResearch.WordTrace tailWord_1374385 prefixEnd_1374385 705720109329710446066825 := by
  unfold tailWord_1374385
  simp only [CollatzResearch.WordTrace]
  refine ⟨50127939125845346115596609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33418626083896897410397739 50127939125845346115596609)
  ·
    refine ⟨37595954344384009586697457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50127939125845346115596609 37595954344384009586697457)
    ·
      refine ⟨28196965758288007190023093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37595954344384009586697457 28196965758288007190023093)
      ·
        refine ⟨2643465539839500674064665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28196965758288007190023093 2643465539839500674064665)
        ·
          refine ⟨1982599154879625505548499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2643465539839500674064665 1982599154879625505548499)
          ·
            refine ⟨2973898732319438258322749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982599154879625505548499 2973898732319438258322749)
            ·
              refine ⟨1115212024619789346871031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2973898732319438258322749 1115212024619789346871031)
              ·
                refine ⟨1672818036929684020306547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115212024619789346871031 1672818036929684020306547)
                ·
                  refine ⟨2509227055394526030459821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672818036929684020306547 2509227055394526030459821)
                  ·
                    refine ⟨940960145772947261422433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509227055394526030459821 940960145772947261422433)
                    ·
                      refine ⟨705720109329710446066825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 940960145772947261422433 705720109329710446066825)
                      ·
                        rfl

theorem cell23_1374385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1374385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374385 prefixEnd_1374385 := by exact prefixLift 1374385
  have htrace : WordTrace (prefixWord ++ tailWord_1374385) baseStart_1374385 baseEnd_1374385 := by
    simpa [prefixWord, tailWord_1374385, baseEnd_1374385] using wordTrace_append hprefix tailTrace_1374385
  have hstable : (prefixWord ++ tailWord_1374385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374385).length < 2 ^ (prefixWord ++ tailWord_1374385).sum := by decide
  have hdescent : baseEnd_1374385 < baseStart_1374385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374414 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_1374414 : Nat := 118140960795 + 1374414 * 2 ^ 59
def prefixEnd_1374414 : Nat := 4983230072969 + 3 ^ 40 * 1374414 * 2
def baseEnd_1374414 : Nat := 705735000268690832604191

theorem tailTrace_1374414 : CollatzResearch.WordTrace tailWord_1374414 prefixEnd_1374414 705735000268690832604191 := by
  unfold tailWord_1374414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6266124605342535508550287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33419331228493522712268197 6266124605342535508550287)
  ·
    refine ⟨9399186908013803262825431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6266124605342535508550287 9399186908013803262825431)
    ·
      refine ⟨14098780362020704894238147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9399186908013803262825431 14098780362020704894238147)
      ·
        refine ⟨21148170543031057341357221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14098780362020704894238147 21148170543031057341357221)
        ·
          refine ⟨3965281976818323251504479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21148170543031057341357221 3965281976818323251504479)
          ·
            refine ⟨5947922965227484877256719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965281976818323251504479 5947922965227484877256719)
            ·
              refine ⟨8921884447841227315885079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5947922965227484877256719 8921884447841227315885079)
              ·
                refine ⟨13382826671761840973827619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8921884447841227315885079 13382826671761840973827619)
                ·
                  refine ⟨20074240007642761460741429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13382826671761840973827619 20074240007642761460741429)
                  ·
                    refine ⟨1881960000716508886944509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20074240007642761460741429 1881960000716508886944509)
                    ·
                      refine ⟨705735000268690832604191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1881960000716508886944509 705735000268690832604191)
                      ·
                        rfl

theorem cell23_1374414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_1374414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374414 prefixEnd_1374414 := by exact prefixLift 1374414
  have htrace : WordTrace (prefixWord ++ tailWord_1374414) baseStart_1374414 baseEnd_1374414 := by
    simpa [prefixWord, tailWord_1374414, baseEnd_1374414] using wordTrace_append hprefix tailTrace_1374414
  have hstable : (prefixWord ++ tailWord_1374414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374414).length < 2 ^ (prefixWord ++ tailWord_1374414).sum := by decide
  have hdescent : baseEnd_1374414 < baseStart_1374414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374417 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 4, 5]
def baseStart_1374417 : Nat := 118140960795 + 1374417 * 2 ^ 59
def prefixEnd_1374417 : Nat := 4983230072969 + 3 ^ 40 * 1374417 * 2
def baseEnd_1374417 : Nat := 235245513570218106955559

theorem tailTrace_1374417 : CollatzResearch.WordTrace tailWord_1374417 prefixEnd_1374417 235245513570218106955559 := by
  unfold tailWord_1374417
  simp only [CollatzResearch.WordTrace]
  refine ⟨50129106261729415580761505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33419404174486277053841003 50129106261729415580761505)
  ·
    refine ⟨37596829696297061685571129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50129106261729415580761505 37596829696297061685571129)
    ·
      refine ⟨28197622272222796264178347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37596829696297061685571129 28197622272222796264178347)
      ·
        refine ⟨42296433408334194396267521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28197622272222796264178347 42296433408334194396267521)
        ·
          refine ⟨31722325056250645797200641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42296433408334194396267521 31722325056250645797200641)
          ·
            refine ⟨23791743792187984347900481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31722325056250645797200641 23791743792187984347900481)
            ·
              refine ⟨17843807844140988260925361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23791743792187984347900481 17843807844140988260925361)
              ·
                refine ⟨13382855883105741195694021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17843807844140988260925361 13382855883105741195694021)
                ·
                  refine ⟨2509285478082326474192629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13382855883105741195694021 2509285478082326474192629)
                  ·
                    refine ⟨235245513570218106955559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2509285478082326474192629 235245513570218106955559)
                    ·
                      rfl

theorem cell23_1374417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_1374417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374417 prefixEnd_1374417 := by exact prefixLift 1374417
  have htrace : WordTrace (prefixWord ++ tailWord_1374417) baseStart_1374417 baseEnd_1374417 := by
    simpa [prefixWord, tailWord_1374417, baseEnd_1374417] using wordTrace_append hprefix tailTrace_1374417
  have hstable : (prefixWord ++ tailWord_1374417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374417).length < 2 ^ (prefixWord ++ tailWord_1374417).sum := by decide
  have hdescent : baseEnd_1374417 < baseStart_1374417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374464 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 3, 4]
def baseStart_1374464 : Nat := 118140960795 + 1374464 * 2 ^ 59
def prefixEnd_1374464 : Nat := 4983230072969 + 3 ^ 40 * 1374464 * 2
def baseEnd_1374464 : Nat := 235253558100471878992987

theorem tailTrace_1374464 : CollatzResearch.WordTrace tailWord_1374464 prefixEnd_1374464 235253558100471878992987 := by
  unfold tailWord_1374464
  simp only [CollatzResearch.WordTrace]
  refine ⟨25065410246279571303861223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33420546995039428405148297 25065410246279571303861223)
  ·
    refine ⟨37598115369419356955791835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25065410246279571303861223 37598115369419356955791835)
    ·
      refine ⟨56397173054129035433687753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37598115369419356955791835 56397173054129035433687753)
      ·
        refine ⟨42297879790596776575265815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56397173054129035433687753 42297879790596776575265815)
        ·
          refine ⟨63446819685895164862898723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42297879790596776575265815 63446819685895164862898723)
          ·
            refine ⟨95170229528842747294348085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63446819685895164862898723 95170229528842747294348085)
            ·
              refine ⟨8922209018329007558845133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95170229528842747294348085 8922209018329007558845133)
              ·
                refine ⟨3345828381873377834566925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8922209018329007558845133 3345828381873377834566925)
                ·
                  refine ⟨1254685643202516687962597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3345828381873377834566925 1254685643202516687962597)
                  ·
                    refine ⟨235253558100471878992987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254685643202516687962597 235253558100471878992987)
                    ·
                      rfl

theorem cell23_1374464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 4].length) (baseStart_1374464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374464 prefixEnd_1374464 := by exact prefixLift 1374464
  have htrace : WordTrace (prefixWord ++ tailWord_1374464) baseStart_1374464 baseEnd_1374464 := by
    simpa [prefixWord, tailWord_1374464, baseEnd_1374464] using wordTrace_append hprefix tailTrace_1374464
  have hstable : (prefixWord ++ tailWord_1374464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374464).length < 2 ^ (prefixWord ++ tailWord_1374464).sum := by decide
  have hdescent : baseEnd_1374464 < baseStart_1374464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374467 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 6]
def baseStart_1374467 : Nat := 118140960795 + 1374467 * 2 ^ 59
def prefixEnd_1374467 : Nat := 4983230072969 + 3 ^ 40 * 1374467 * 2
def baseEnd_1374467 : Nat := 705762214743379125241447

theorem tailTrace_1374467 : CollatzResearch.WordTrace tailWord_1374467 prefixEnd_1374467 705762214743379125241447 := by
  unfold tailWord_1374467
  simp only [CollatzResearch.WordTrace]
  refine ⟨50130929911548274120081655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33420619941032182746721103 50130929911548274120081655)
  ·
    refine ⟨75196394867322411180122483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50130929911548274120081655 75196394867322411180122483)
    ·
      refine ⟨112794592300983616770183725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75196394867322411180122483 112794592300983616770183725)
      ·
        refine ⟨42297972112868856288818897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112794592300983616770183725 42297972112868856288818897)
        ·
          refine ⟨31723479084651642216614173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42297972112868856288818897 31723479084651642216614173)
          ·
            refine ⟨11896304656744365831230315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31723479084651642216614173 11896304656744365831230315)
            ·
              refine ⟨17844456985116548746845473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11896304656744365831230315 17844456985116548746845473)
              ·
                refine ⟨13383342738837411560134105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17844456985116548746845473 13383342738837411560134105)
                ·
                  refine ⟨10037507054128058670100579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13383342738837411560134105 10037507054128058670100579)
                  ·
                    refine ⟨15056260581192088005150869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10037507054128058670100579 15056260581192088005150869)
                    ·
                      refine ⟨705762214743379125241447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15056260581192088005150869 705762214743379125241447)
                      ·
                        rfl

theorem cell23_1374467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_1374467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374467 prefixEnd_1374467 := by exact prefixLift 1374467
  have htrace : WordTrace (prefixWord ++ tailWord_1374467) baseStart_1374467 baseEnd_1374467 := by
    simpa [prefixWord, tailWord_1374467, baseEnd_1374467] using wordTrace_append hprefix tailTrace_1374467
  have hstable : (prefixWord ++ tailWord_1374467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374467).length < 2 ^ (prefixWord ++ tailWord_1374467).sum := by decide
  have hdescent : baseEnd_1374467 < baseStart_1374467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374474 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1374474 : Nat := 118140960795 + 1374474 * 2 ^ 59
def prefixEnd_1374474 : Nat := 4983230072969 + 3 ^ 40 * 1374474 * 2
def baseEnd_1374474 : Nat := 705765809107960597853915

theorem tailTrace_1374474 : CollatzResearch.WordTrace tailWord_1374474 prefixEnd_1374474 705765809107960597853915 := by
  unfold tailWord_1374474
  simp only [CollatzResearch.WordTrace]
  refine ⟨12532796305630728578896619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33420790148348609543724317 12532796305630728578896619)
  ·
    refine ⟨18799194458446092868344929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12532796305630728578896619 18799194458446092868344929)
    ·
      refine ⟨14099395843834569651258697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18799194458446092868344929 14099395843834569651258697)
      ·
        refine ⟨10574546882875927238444023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14099395843834569651258697 10574546882875927238444023)
        ·
          refine ⟨15861820324313890857666035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10574546882875927238444023 15861820324313890857666035)
          ·
            refine ⟨23792730486470836286499053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15861820324313890857666035 23792730486470836286499053)
            ·
              refine ⟨8922273932426563607437145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23792730486470836286499053 8922273932426563607437145)
              ·
                refine ⟨6691705449319922705577859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8922273932426563607437145 6691705449319922705577859)
                ·
                  refine ⟨10037558173979884058366789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6691705449319922705577859 10037558173979884058366789)
                  ·
                    refine ⟨1882042157621228260943773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10037558173979884058366789 1882042157621228260943773)
                    ·
                      refine ⟨705765809107960597853915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1882042157621228260943773 705765809107960597853915)
                      ·
                        rfl

theorem cell23_1374474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1374474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374474 prefixEnd_1374474 := by exact prefixLift 1374474
  have htrace : WordTrace (prefixWord ++ tailWord_1374474) baseStart_1374474 baseEnd_1374474 := by
    simpa [prefixWord, tailWord_1374474, baseEnd_1374474] using wordTrace_append hprefix tailTrace_1374474
  have hstable : (prefixWord ++ tailWord_1374474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374474).length < 2 ^ (prefixWord ++ tailWord_1374474).sum := by decide
  have hdescent : baseEnd_1374474 < baseStart_1374474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374524 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1374524 : Nat := 118140960795 + 1374524 * 2 ^ 59
def prefixEnd_1374524 : Nat := 4983230072969 + 3 ^ 40 * 1374524 * 2
def baseEnd_1374524 : Nat := 235263827713561800742895

theorem tailTrace_1374524 : CollatzResearch.WordTrace tailWord_1374524 prefixEnd_1374524 235263827713561800742895 := by
  unfold tailWord_1374524
  simp only [CollatzResearch.WordTrace]
  refine ⟨25066504436170886427453313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33422005914894515236604417 25066504436170886427453313)
  ·
    refine ⟨18799878327128164820589985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25066504436170886427453313 18799878327128164820589985)
    ·
      refine ⟨14099908745346123615442489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18799878327128164820589985 14099908745346123615442489)
      ·
        refine ⟨10574931559009592711581867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14099908745346123615442489 10574931559009592711581867)
        ·
          refine ⟨15862397338514389067372801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10574931559009592711581867 15862397338514389067372801)
          ·
            refine ⟨11896798003885791800529601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15862397338514389067372801 11896798003885791800529601)
            ·
              refine ⟨8922598502914343850397201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11896798003885791800529601 8922598502914343850397201)
              ·
                refine ⟨6691948877185757887797901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8922598502914343850397201 6691948877185757887797901)
                ·
                  refine ⟨2509480828944659207924213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6691948877185757887797901 2509480828944659207924213)
                  ·
                    refine ⟨235263827713561800742895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2509480828944659207924213 235263827713561800742895)
                    ·
                      rfl

theorem cell23_1374524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1374524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374524 prefixEnd_1374524 := by exact prefixLift 1374524
  have htrace : WordTrace (prefixWord ++ tailWord_1374524) baseStart_1374524 baseEnd_1374524 := by
    simpa [prefixWord, tailWord_1374524, baseEnd_1374524] using wordTrace_append hprefix tailTrace_1374524
  have hstable : (prefixWord ++ tailWord_1374524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374524).length < 2 ^ (prefixWord ++ tailWord_1374524).sum := by decide
  have hdescent : baseEnd_1374524 < baseStart_1374524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374548 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_1374548 : Nat := 118140960795 + 1374548 * 2 ^ 59
def prefixEnd_1374548 : Nat := 4983230072969 + 3 ^ 40 * 1374548 * 2
def baseEnd_1374548 : Nat := 705803806676393308328575

theorem tailTrace_1374548 : CollatzResearch.WordTrace tailWord_1374548 prefixEnd_1374548 705803806676393308328575 := by
  unfold tailWord_1374548
  simp only [CollatzResearch.WordTrace]
  refine ⟨25066942112127412476890149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33422589482836549969186865 25066942112127412476890149)
  ·
    refine ⟨4700051646023889839416903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25066942112127412476890149 4700051646023889839416903)
    ·
      refine ⟨7050077469035834759125355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700051646023889839416903 7050077469035834759125355)
      ·
        refine ⟨10575116203553752138688033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7050077469035834759125355 10575116203553752138688033)
        ·
          refine ⟨7931337152665314104016025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10575116203553752138688033 7931337152665314104016025)
          ·
            refine ⟨5948502864498985578012019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7931337152665314104016025 5948502864498985578012019)
            ·
              refine ⟨8922754296748478367018029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948502864498985578012019 8922754296748478367018029)
              ·
                refine ⟨3346032861280679387631761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8922754296748478367018029 3346032861280679387631761)
                ·
                  refine ⟨2509524645960509540723821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3346032861280679387631761 2509524645960509540723821)
                  ·
                    refine ⟨941071742235191077771433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509524645960509540723821 941071742235191077771433)
                    ·
                      refine ⟨705803806676393308328575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941071742235191077771433 705803806676393308328575)
                      ·
                        rfl

theorem cell23_1374548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_1374548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374548 prefixEnd_1374548 := by exact prefixLift 1374548
  have htrace : WordTrace (prefixWord ++ tailWord_1374548) baseStart_1374548 baseEnd_1374548 := by
    simpa [prefixWord, tailWord_1374548, baseEnd_1374548] using wordTrace_append hprefix tailTrace_1374548
  have hstable : (prefixWord ++ tailWord_1374548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374548).length < 2 ^ (prefixWord ++ tailWord_1374548).sum := by decide
  have hdescent : baseEnd_1374548 < baseStart_1374548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374595 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 3, 2, 2]
def baseStart_1374595 : Nat := 118140960795 + 1374595 * 2 ^ 59
def prefixEnd_1374595 : Nat := 4983230072969 + 3 ^ 40 * 1374595 * 2
def baseEnd_1374595 : Nat := 705827940267154624440859

theorem tailTrace_1374595 : CollatzResearch.WordTrace tailWord_1374595 prefixEnd_1374595 705827940267154624440859 := by
  unfold tailWord_1374595
  simp only [CollatzResearch.WordTrace]
  refine ⟨50135598455084551980741239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33423732303389701320494159 50135598455084551980741239)
  ·
    refine ⟨75203397682626827971111859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50135598455084551980741239 75203397682626827971111859)
    ·
      refine ⟨112805096523940241956667789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75203397682626827971111859 112805096523940241956667789)
      ·
        refine ⟨42301911196477590733750421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112805096523940241956667789 42301911196477590733750421)
        ·
          refine ⟨1982902087334887065644551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42301911196477590733750421 1982902087334887065644551)
          ·
            refine ⟨2974353131002330598466827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982902087334887065644551 2974353131002330598466827)
            ·
              refine ⟨4461529696503495897700241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974353131002330598466827 4461529696503495897700241)
              ·
                refine ⟨3346147272377621923275181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461529696503495897700241 3346147272377621923275181)
                ·
                  refine ⟨1254805227141608221228193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3346147272377621923275181 1254805227141608221228193)
                  ·
                    refine ⟨941103920356206165921145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1254805227141608221228193 941103920356206165921145)
                    ·
                      refine ⟨705827940267154624440859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941103920356206165921145 705827940267154624440859)
                      ·
                        rfl

theorem cell23_1374595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_1374595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374595 prefixEnd_1374595 := by exact prefixLift 1374595
  have htrace : WordTrace (prefixWord ++ tailWord_1374595) baseStart_1374595 baseEnd_1374595 := by
    simpa [prefixWord, tailWord_1374595, baseEnd_1374595] using wordTrace_append hprefix tailTrace_1374595
  have hstable : (prefixWord ++ tailWord_1374595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374595).length < 2 ^ (prefixWord ++ tailWord_1374595).sum := by decide
  have hdescent : baseEnd_1374595 < baseStart_1374595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374601 : List Nat := [1, 2, 1, 1, 6, 2, 3, 7]
def baseStart_1374601 : Nat := 118140960795 + 1374601 * 2 ^ 59
def prefixEnd_1374601 : Nat := 4983230072969 + 3 ^ 40 * 1374601 * 2
def baseEnd_1374601 : Nat := 26141889672262281517253

theorem tailTrace_1374601 : CollatzResearch.WordTrace tailWord_1374601 prefixEnd_1374601 26141889672262281517253 := by
  unfold tailWord_1374601
  simp only [CollatzResearch.WordTrace]
  refine ⟨50135817293062815005459657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33423878195375210003639771 50135817293062815005459657)
  ·
    refine ⟨37601862969797111254094743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50135817293062815005459657 37601862969797111254094743)
    ·
      refine ⟨56402794454695666881142115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37601862969797111254094743 56402794454695666881142115)
      ·
        refine ⟨84604191682043500321713173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56402794454695666881142115 84604191682043500321713173)
        ·
          refine ⟨3965821485095789077580305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84604191682043500321713173 3965821485095789077580305)
          ·
            refine ⟨2974366113821841808185229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3965821485095789077580305 2974366113821841808185229)
            ·
              refine ⟨1115387292683190678069461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2974366113821841808185229 1115387292683190678069461)
              ·
                refine ⟨26141889672262281517253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1115387292683190678069461 26141889672262281517253)
                ·
                  rfl

theorem cell23_1374601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 7].length) (baseStart_1374601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374601 prefixEnd_1374601 := by exact prefixLift 1374601
  have htrace : WordTrace (prefixWord ++ tailWord_1374601) baseStart_1374601 baseEnd_1374601 := by
    simpa [prefixWord, tailWord_1374601, baseEnd_1374601] using wordTrace_append hprefix tailTrace_1374601
  have hstable : (prefixWord ++ tailWord_1374601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374601).length < 2 ^ (prefixWord ++ tailWord_1374601).sum := by decide
  have hdescent : baseEnd_1374601 < baseStart_1374601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374612 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_1374612 : Nat := 118140960795 + 1374612 * 2 ^ 59
def prefixEnd_1374612 : Nat := 4983230072969 + 3 ^ 40 * 1374612 * 2
def baseEnd_1374612 : Nat := 705836669438281057928281

theorem tailTrace_1374612 : CollatzResearch.WordTrace tailWord_1374612 prefixEnd_1374612 705836669438281057928281 := by
  unfold tailWord_1374612
  simp only [CollatzResearch.WordTrace]
  refine ⟨25068109248011481942055045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33424145664015309256073393 25068109248011481942055045)
  ·
    refine ⟨4700270484002152864135321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25068109248011481942055045 4700270484002152864135321)
    ·
      refine ⟨3525202863001614648101491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4700270484002152864135321 3525202863001614648101491)
      ·
        refine ⟨5287804294502421972152237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3525202863001614648101491 5287804294502421972152237)
        ·
          refine ⟨1982926610438408239557089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5287804294502421972152237 1982926610438408239557089)
          ·
            refine ⟨1487194957828806179667817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1982926610438408239557089 1487194957828806179667817)
            ·
              refine ⟨1115396218371604634750863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487194957828806179667817 1115396218371604634750863)
              ·
                refine ⟨1673094327557406952126295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115396218371604634750863 1673094327557406952126295)
                ·
                  refine ⟨2509641491336110428189443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673094327557406952126295 2509641491336110428189443)
                  ·
                    refine ⟨3764462237004165642284165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2509641491336110428189443 3764462237004165642284165)
                    ·
                      refine ⟨705836669438281057928281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3764462237004165642284165 705836669438281057928281)
                      ·
                        rfl

theorem cell23_1374612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_1374612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374612 prefixEnd_1374612 := by exact prefixLift 1374612
  have htrace : WordTrace (prefixWord ++ tailWord_1374612) baseStart_1374612 baseEnd_1374612 := by
    simpa [prefixWord, tailWord_1374612, baseEnd_1374612] using wordTrace_append hprefix tailTrace_1374612
  have hstable : (prefixWord ++ tailWord_1374612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374612).length < 2 ^ (prefixWord ++ tailWord_1374612).sum := by decide
  have hdescent : baseEnd_1374612 < baseStart_1374612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374622 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1374622 : Nat := 118140960795 + 1374622 * 2 ^ 59
def prefixEnd_1374622 : Nat := 4983230072969 + 3 ^ 40 * 1374622 * 2
def baseEnd_1374622 : Nat := 235280601414942006267745

theorem tailTrace_1374622 : CollatzResearch.WordTrace tailWord_1374622 prefixEnd_1374622 235280601414942006267745 := by
  unfold tailWord_1374622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267072903248341948996765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33424388817324490394649413 6267072903248341948996765)
  ·
    refine ⟨2350152338718128230873787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6267072903248341948996765 2350152338718128230873787)
    ·
      refine ⟨3525228508077192346310681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2350152338718128230873787 3525228508077192346310681)
      ·
        refine ⟨2643921381057894259733011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3525228508077192346310681 2643921381057894259733011)
        ·
          refine ⟨3965882071586841389599517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643921381057894259733011 3965882071586841389599517)
          ·
            refine ⟨1487205776845065521099819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3965882071586841389599517 1487205776845065521099819)
            ·
              refine ⟨2230808665267598281649729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487205776845065521099819 2230808665267598281649729)
              ·
                refine ⟨1673106498950698711237297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2230808665267598281649729 1673106498950698711237297)
                ·
                  refine ⟨1254829874213024033427973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1673106498950698711237297 1254829874213024033427973)
                  ·
                    refine ⟨235280601414942006267745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1254829874213024033427973 235280601414942006267745)
                    ·
                      rfl

theorem cell23_1374622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1374622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374622 prefixEnd_1374622 := by exact prefixLift 1374622
  have htrace : WordTrace (prefixWord ++ tailWord_1374622) baseStart_1374622 baseEnd_1374622 := by
    simpa [prefixWord, tailWord_1374622, baseEnd_1374622] using wordTrace_append hprefix tailTrace_1374622
  have hstable : (prefixWord ++ tailWord_1374622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374622).length < 2 ^ (prefixWord ++ tailWord_1374622).sum := by decide
  have hdescent : baseEnd_1374622 < baseStart_1374622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374645 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1374645 : Nat := 118140960795 + 1374645 * 2 ^ 59
def prefixEnd_1374645 : Nat := 4983230072969 + 3 ^ 40 * 1374645 * 2
def baseEnd_1374645 : Nat := 705853614299879428815629

theorem tailTrace_1374645 : CollatzResearch.WordTrace tailWord_1374645 prefixEnd_1374645 705853614299879428815629 := by
  unfold tailWord_1374645
  simp only [CollatzResearch.WordTrace]
  refine ⟨50137422104903410520061389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33424948069935607013374259 50137422104903410520061389)
  ·
    refine ⟨18801533289338778945023021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50137422104903410520061389 18801533289338778945023021)
    ·
      refine ⟨7050574983502042104383633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18801533289338778945023021 7050574983502042104383633)
      ·
        refine ⟨5287931237626531578287725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7050574983502042104383633 5287931237626531578287725)
        ·
          refine ⟨1982974214109949341857897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5287931237626531578287725 1982974214109949341857897)
          ·
            refine ⟨1487230660582462006393423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1982974214109949341857897 1487230660582462006393423)
            ·
              refine ⟨2230845990873693009590135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487230660582462006393423 2230845990873693009590135)
              ·
                refine ⟨3346268986310539514385203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230845990873693009590135 3346268986310539514385203)
                ·
                  refine ⟨5019403479465809271577805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346268986310539514385203 5019403479465809271577805)
                  ·
                    refine ⟨1882276304799678476841677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5019403479465809271577805 1882276304799678476841677)
                    ·
                      refine ⟨705853614299879428815629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1882276304799678476841677 705853614299879428815629)
                      ·
                        rfl

theorem cell23_1374645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1374645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374645 prefixEnd_1374645 := by exact prefixLift 1374645
  have htrace : WordTrace (prefixWord ++ tailWord_1374645) baseStart_1374645 baseEnd_1374645 := by
    simpa [prefixWord, tailWord_1374645, baseEnd_1374645] using wordTrace_append hprefix tailTrace_1374645
  have hstable : (prefixWord ++ tailWord_1374645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374645).length < 2 ^ (prefixWord ++ tailWord_1374645).sum := by decide
  have hdescent : baseEnd_1374645 < baseStart_1374645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374651 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 7, 4, 2]
def baseStart_1374651 : Nat := 118140960795 + 1374651 * 2 ^ 59
def prefixEnd_1374651 : Nat := 4983230072969 + 3 ^ 40 * 1374651 * 2
def baseEnd_1374651 : Nat := 705856695183806405340601

theorem tailTrace_1374651 : CollatzResearch.WordTrace tailWord_1374651 prefixEnd_1374651 705856695183806405340601 := by
  unfold tailWord_1374651
  simp only [CollatzResearch.WordTrace]
  refine ⟨50137640942881673544779807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33425093961921115696519871 50137640942881673544779807)
  ·
    refine ⟨75206461414322510317169711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50137640942881673544779807 75206461414322510317169711)
    ·
      refine ⟨112809692121483765475754567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75206461414322510317169711 112809692121483765475754567)
      ·
        refine ⟨169214538182225648213631851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112809692121483765475754567 169214538182225648213631851)
        ·
          refine ⟨253821807273338472320447777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169214538182225648213631851 253821807273338472320447777)
          ·
            refine ⟨190366355455003854240335833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253821807273338472320447777 190366355455003854240335833)
            ·
              refine ⟨142774766591252890680251875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190366355455003854240335833 142774766591252890680251875)
              ·
                refine ⟨214162149886879336020377813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142774766591252890680251875 214162149886879336020377813)
                ·
                  refine ⟨5019425387973734437977605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 214162149886879336020377813 5019425387973734437977605)
                  ·
                    refine ⟨941142260245075207120801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019425387973734437977605 941142260245075207120801)
                    ·
                      refine ⟨705856695183806405340601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941142260245075207120801 705856695183806405340601)
                      ·
                        rfl

theorem cell23_1374651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 4, 2].length) (baseStart_1374651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374651 prefixEnd_1374651 := by exact prefixLift 1374651
  have htrace : WordTrace (prefixWord ++ tailWord_1374651) baseStart_1374651 baseEnd_1374651 := by
    simpa [prefixWord, tailWord_1374651, baseEnd_1374651] using wordTrace_append hprefix tailTrace_1374651
  have hstable : (prefixWord ++ tailWord_1374651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374651).length < 2 ^ (prefixWord ++ tailWord_1374651).sum := by decide
  have hdescent : baseEnd_1374651 < baseStart_1374651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374685 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_1374685 : Nat := 118140960795 + 1374685 * 2 ^ 59
def prefixEnd_1374685 : Nat := 4983230072969 + 3 ^ 40 * 1374685 * 2
def baseEnd_1374685 : Nat := 705874153526059272315445

theorem tailTrace_1374685 : CollatzResearch.WordTrace tailWord_1374685 prefixEnd_1374685 705874153526059272315445 := by
  unfold tailWord_1374685
  simp only [CollatzResearch.WordTrace]
  refine ⟨50138881024758497351517509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33425920683172331567678339 50138881024758497351517509)
  ·
    refine ⟨9401040192142218253409533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50138881024758497351517509 9401040192142218253409533)
    ·
      refine ⟨3525390072053331845028575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9401040192142218253409533 3525390072053331845028575)
      ·
        refine ⟨5288085108079997767542863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3525390072053331845028575 5288085108079997767542863)
        ·
          refine ⟨7932127662119996651314295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288085108079997767542863 7932127662119996651314295)
          ·
            refine ⟨11898191493179994976971443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7932127662119996651314295 11898191493179994976971443)
            ·
              refine ⟨17847287239769992465457165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11898191493179994976971443 17847287239769992465457165)
              ·
                refine ⟨6692732714913747174546437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17847287239769992465457165 6692732714913747174546437)
                ·
                  refine ⟨1254887384046327595227457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6692732714913747174546437 1254887384046327595227457)
                  ·
                    refine ⟨941165538034745696420593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1254887384046327595227457 941165538034745696420593)
                    ·
                      refine ⟨705874153526059272315445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941165538034745696420593 705874153526059272315445)
                      ·
                        rfl

theorem cell23_1374685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_1374685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374685 prefixEnd_1374685 := by exact prefixLift 1374685
  have htrace : WordTrace (prefixWord ++ tailWord_1374685) baseStart_1374685 baseEnd_1374685 := by
    simpa [prefixWord, tailWord_1374685, baseEnd_1374685] using wordTrace_append hprefix tailTrace_1374685
  have hstable : (prefixWord ++ tailWord_1374685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374685).length < 2 ^ (prefixWord ++ tailWord_1374685).sum := by decide
  have hdescent : baseEnd_1374685 < baseStart_1374685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374702 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_1374702 : Nat := 118140960795 + 1374702 * 2 ^ 59
def prefixEnd_1374702 : Nat := 4983230072969 + 3 ^ 40 * 1374702 * 2
def baseEnd_1374702 : Nat := 705882882697185705802867

theorem tailTrace_1374702 : CollatzResearch.WordTrace tailWord_1374702 prefixEnd_1374702 705882882697185705802867 := by
  unfold tailWord_1374702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267437633212113656860795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33426334043797939503257573 6267437633212113656860795)
  ·
    refine ⟨9401156449818170485291193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6267437633212113656860795 9401156449818170485291193)
    ·
      refine ⟨7050867337363627863968395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9401156449818170485291193 7050867337363627863968395)
      ·
        refine ⟨10576301006045441795952593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7050867337363627863968395 10576301006045441795952593)
        ·
          refine ⟨7932225754534081346964445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10576301006045441795952593 7932225754534081346964445)
          ·
            refine ⟨2974584657950280505111667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7932225754534081346964445 2974584657950280505111667)
            ·
              refine ⟨4461876986925420757667501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974584657950280505111667 4461876986925420757667501)
              ·
                refine ⟨1673203870097032784125313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4461876986925420757667501 1673203870097032784125313)
                ·
                  refine ⟨1254902902572774588093985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1673203870097032784125313 1254902902572774588093985)
                  ·
                    refine ⟨941177176929580941070489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1254902902572774588093985 941177176929580941070489)
                    ·
                      refine ⟨705882882697185705802867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941177176929580941070489 705882882697185705802867)
                      ·
                        rfl

theorem cell23_1374702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_1374702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374702 prefixEnd_1374702 := by exact prefixLift 1374702
  have htrace : WordTrace (prefixWord ++ tailWord_1374702) baseStart_1374702 baseEnd_1374702 := by
    simpa [prefixWord, tailWord_1374702, baseEnd_1374702] using wordTrace_append hprefix tailTrace_1374702
  have hstable : (prefixWord ++ tailWord_1374702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374702).length < 2 ^ (prefixWord ++ tailWord_1374702).sum := by decide
  have hdescent : baseEnd_1374702 < baseStart_1374702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374731 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 5]
def baseStart_1374731 : Nat := 118140960795 + 1374731 * 2 ^ 59
def prefixEnd_1374731 : Nat := 4983230072969 + 3 ^ 40 * 1374731 * 2
def baseEnd_1374731 : Nat := 705897773636166092340233

theorem tailTrace_1374731 : CollatzResearch.WordTrace tailWord_1374731 prefixEnd_1374731 705897773636166092340233 := by
  unfold tailWord_1374731
  simp only [CollatzResearch.WordTrace]
  refine ⟨50140558782591847207692047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33427039188394564805128031 50140558782591847207692047)
  ·
    refine ⟨75210838173887770811538071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50140558782591847207692047 75210838173887770811538071)
    ·
      refine ⟨112816257260831656217307107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75210838173887770811538071 112816257260831656217307107)
      ·
        refine ⟨169224385891247484325960661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112816257260831656217307107 169224385891247484325960661)
        ·
          refine ⟨3966196544326112913889703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 169224385891247484325960661 3966196544326112913889703)
          ·
            refine ⟨5949294816489169370834555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966196544326112913889703 5949294816489169370834555)
            ·
              refine ⟨8923942224733754056251833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949294816489169370834555 8923942224733754056251833)
              ·
                refine ⟨6692956668550315542188875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8923942224733754056251833 6692956668550315542188875)
                ·
                  refine ⟨10039435002825473313283313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6692956668550315542188875 10039435002825473313283313)
                  ·
                    refine ⟨7529576252119104984962485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10039435002825473313283313 7529576252119104984962485)
                    ·
                      refine ⟨705897773636166092340233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7529576252119104984962485 705897773636166092340233)
                      ·
                        rfl

theorem cell23_1374731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 5].length) (baseStart_1374731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374731 prefixEnd_1374731 := by exact prefixLift 1374731
  have htrace : WordTrace (prefixWord ++ tailWord_1374731) baseStart_1374731 baseEnd_1374731 := by
    simpa [prefixWord, tailWord_1374731, baseEnd_1374731] using wordTrace_append hprefix tailTrace_1374731
  have hstable : (prefixWord ++ tailWord_1374731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374731).length < 2 ^ (prefixWord ++ tailWord_1374731).sum := by decide
  have hdescent : baseEnd_1374731 < baseStart_1374731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374778 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_1374778 : Nat := 118140960795 + 1374778 * 2 ^ 59
def prefixEnd_1374778 : Nat := 4983230072969 + 3 ^ 40 * 1374778 * 2
def baseEnd_1374778 : Nat := 705921907226927408452517

theorem tailTrace_1374778 : CollatzResearch.WordTrace tailWord_1374778 prefixEnd_1374778 705921907226927408452517 := by
  unfold tailWord_1374778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12535568253355393558663247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33428182008947716156435325 12535568253355393558663247)
  ·
    refine ⟨18803352380033090337994871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12535568253355393558663247 18803352380033090337994871)
    ·
      refine ⟨28205028570049635506992307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18803352380033090337994871 28205028570049635506992307)
      ·
        refine ⟨42307542855074453260488461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28205028570049635506992307 42307542855074453260488461)
        ·
          refine ⟨15865328570652919972683173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42307542855074453260488461 15865328570652919972683173)
          ·
            refine ⟨2974749106997422494878095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15865328570652919972683173 2974749106997422494878095)
            ·
              refine ⟨4462123660496133742317143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974749106997422494878095 4462123660496133742317143)
              ·
                refine ⟨6693185490744200613475715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462123660496133742317143 6693185490744200613475715)
                ·
                  refine ⟨10039778236116300920213573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693185490744200613475715 10039778236116300920213573)
                  ·
                    refine ⟨1882458419271806422540045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10039778236116300920213573 1882458419271806422540045)
                    ·
                      refine ⟨705921907226927408452517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1882458419271806422540045 705921907226927408452517)
                      ·
                        rfl

theorem cell23_1374778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_1374778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374778 prefixEnd_1374778 := by exact prefixLift 1374778
  have htrace : WordTrace (prefixWord ++ tailWord_1374778) baseStart_1374778 baseEnd_1374778 := by
    simpa [prefixWord, tailWord_1374778, baseEnd_1374778] using wordTrace_append hprefix tailTrace_1374778
  have hstable : (prefixWord ++ tailWord_1374778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374778).length < 2 ^ (prefixWord ++ tailWord_1374778).sum := by decide
  have hdescent : baseEnd_1374778 < baseStart_1374778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374798 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_1374798 : Nat := 118140960795 + 1374798 * 2 ^ 59
def prefixEnd_1374798 : Nat := 4983230072969 + 3 ^ 40 * 1374798 * 2
def baseEnd_1374798 : Nat := 78436908537779703355825

theorem tailTrace_1374798 : CollatzResearch.WordTrace tailWord_1374798 prefixEnd_1374798 78436908537779703355825 := by
  unfold tailWord_1374798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267875309168639706297631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33428668315566078433587365 6267875309168639706297631)
  ·
    refine ⟨9401812963752959559446447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6267875309168639706297631 9401812963752959559446447)
    ·
      refine ⟨14102719445629439339169671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9401812963752959559446447 14102719445629439339169671)
      ·
        refine ⟨21154079168444159008754507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14102719445629439339169671 21154079168444159008754507)
        ·
          refine ⟨31731118752666238513131761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21154079168444159008754507 31731118752666238513131761)
          ·
            refine ⟨23798339064499678884848821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31731118752666238513131761 23798339064499678884848821)
            ·
              refine ⟨2231094287296844895454577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23798339064499678884848821 2231094287296844895454577)
              ·
                refine ⟨1673320715472633671590933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231094287296844895454577 1673320715472633671590933)
                ·
                  refine ⟨78436908537779703355825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1673320715472633671590933 78436908537779703355825)
                  ·
                    rfl

theorem cell23_1374798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_1374798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374798 prefixEnd_1374798 := by exact prefixLift 1374798
  have htrace : WordTrace (prefixWord ++ tailWord_1374798) baseStart_1374798 baseEnd_1374798 := by
    simpa [prefixWord, tailWord_1374798, baseEnd_1374798] using wordTrace_append hprefix tailTrace_1374798
  have hstable : (prefixWord ++ tailWord_1374798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374798).length < 2 ^ (prefixWord ++ tailWord_1374798).sum := by decide
  have hdescent : baseEnd_1374798 < baseStart_1374798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374801 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_1374801 : Nat := 118140960795 + 1374801 * 2 ^ 59
def prefixEnd_1374801 : Nat := 4983230072969 + 3 ^ 40 * 1374801 * 2
def baseEnd_1374801 : Nat := 705933717281980818464911

theorem tailTrace_1374801 : CollatzResearch.WordTrace tailWord_1374801 prefixEnd_1374801 705933717281980818464911 := by
  unfold tailWord_1374801
  simp only [CollatzResearch.WordTrace]
  refine ⟨50143111892338249162740257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33428741261558832775160171 50143111892338249162740257)
  ·
    refine ⟨37607333919253686872055193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50143111892338249162740257 37607333919253686872055193)
    ·
      refine ⟨28205500439440265154041395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37607333919253686872055193 28205500439440265154041395)
      ·
        refine ⟨42308250659160397731062093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28205500439440265154041395 42308250659160397731062093)
        ·
          refine ⟨15865593997185149149148285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42308250659160397731062093 15865593997185149149148285)
          ·
            refine ⟨5949597748944430930930607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15865593997185149149148285 5949597748944430930930607)
            ·
              refine ⟨8924396623416646396395911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949597748944430930930607 8924396623416646396395911)
              ·
                refine ⟨13386594935124969594593867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8924396623416646396395911 13386594935124969594593867)
                ·
                  refine ⟨20079892402687454391890801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13386594935124969594593867 20079892402687454391890801)
                  ·
                    refine ⟨15059919302015590793918101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20079892402687454391890801 15059919302015590793918101)
                    ·
                      refine ⟨705933717281980818464911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15059919302015590793918101 705933717281980818464911)
                      ·
                        rfl

theorem cell23_1374801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_1374801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374801 prefixEnd_1374801 := by exact prefixLift 1374801
  have htrace : WordTrace (prefixWord ++ tailWord_1374801) baseStart_1374801 baseEnd_1374801 := by
    simpa [prefixWord, tailWord_1374801, baseEnd_1374801] using wordTrace_append hprefix tailTrace_1374801
  have hstable : (prefixWord ++ tailWord_1374801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374801).length < 2 ^ (prefixWord ++ tailWord_1374801).sum := by decide
  have hdescent : baseEnd_1374801 < baseStart_1374801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374828 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_1374828 : Nat := 118140960795 + 1374828 * 2 ^ 59
def prefixEnd_1374828 : Nat := 4983230072969 + 3 ^ 40 * 1374828 * 2
def baseEnd_1374828 : Nat := 235315860419884070942429

theorem tailTrace_1374828 : CollatzResearch.WordTrace tailWord_1374828 prefixEnd_1374828 235315860419884070942429 := by
  unfold tailWord_1374828
  simp only [CollatzResearch.WordTrace]
  refine ⟨25072048331620216386986569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33429397775493621849315425 25072048331620216386986569)
  ·
    refine ⟨18804036248715162290239927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25072048331620216386986569 18804036248715162290239927)
    ·
      refine ⟨28206054373072743435359891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18804036248715162290239927 28206054373072743435359891)
      ·
        refine ⟨42309081559609115153039837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28206054373072743435359891 42309081559609115153039837)
        ·
          refine ⟨15865905584853418182389939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42309081559609115153039837 15865905584853418182389939)
          ·
            refine ⟨23798858377280127273584909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15865905584853418182389939 23798858377280127273584909)
            ·
              refine ⟨8924571891480047727594341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23798858377280127273584909 8924571891480047727594341)
              ·
                refine ⟨1673357229652508948923939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8924571891480047727594341 1673357229652508948923939)
                ·
                  refine ⟨2510035844478763423385909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673357229652508948923939 2510035844478763423385909)
                  ·
                    refine ⟨235315860419884070942429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2510035844478763423385909 235315860419884070942429)
                    ·
                      rfl

theorem cell23_1374828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_1374828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374828 prefixEnd_1374828 := by exact prefixLift 1374828
  have htrace : WordTrace (prefixWord ++ tailWord_1374828) baseStart_1374828 baseEnd_1374828 := by
    simpa [prefixWord, tailWord_1374828, baseEnd_1374828] using wordTrace_append hprefix tailTrace_1374828
  have hstable : (prefixWord ++ tailWord_1374828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374828).length < 2 ^ (prefixWord ++ tailWord_1374828).sum := by decide
  have hdescent : baseEnd_1374828 < baseStart_1374828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374852 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_1374852 : Nat := 118140960795 + 1374852 * 2 ^ 59
def prefixEnd_1374852 : Nat := 4983230072969 + 3 ^ 40 * 1374852 * 2
def baseEnd_1374852 : Nat := 705959904795360118927177

theorem tailTrace_1374852 : CollatzResearch.WordTrace tailWord_1374852 prefixEnd_1374852 705959904795360118927177 := by
  unfold tailWord_1374852
  simp only [CollatzResearch.WordTrace]
  refine ⟨25072486007576742436423405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33429981343435656581897873 25072486007576742436423405)
  ·
    refine ⟨9402182252841278413658777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25072486007576742436423405 9402182252841278413658777)
    ·
      refine ⟨7051636689630958810244083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9402182252841278413658777 7051636689630958810244083)
      ·
        refine ⟨10577455034446438215366125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7051636689630958810244083 10577455034446438215366125)
        ·
          refine ⟨3966545637917414330762297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10577455034446438215366125 3966545637917414330762297)
          ·
            refine ⟨2974909228438060748071723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3966545637917414330762297 2974909228438060748071723)
            ·
              refine ⟨4462363842657091122107585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974909228438060748071723 4462363842657091122107585)
              ·
                refine ⟨3346772881992818341580689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4462363842657091122107585 3346772881992818341580689)
                ·
                  refine ⟨2510079661494613756185517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3346772881992818341580689 2510079661494613756185517)
                  ·
                    refine ⟨941279873060480158569569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2510079661494613756185517 941279873060480158569569)
                    ·
                      refine ⟨705959904795360118927177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941279873060480158569569 705959904795360118927177)
                      ·
                        rfl

theorem cell23_1374852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_1374852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374852 prefixEnd_1374852 := by exact prefixLift 1374852
  have htrace : WordTrace (prefixWord ++ tailWord_1374852) baseStart_1374852 baseEnd_1374852 := by
    simpa [prefixWord, tailWord_1374852, baseEnd_1374852] using wordTrace_append hprefix tailTrace_1374852
  have hstable : (prefixWord ++ tailWord_1374852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374852).length < 2 ^ (prefixWord ++ tailWord_1374852).sum := by decide
  have hdescent : baseEnd_1374852 < baseStart_1374852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374916 : List Nat := [2, 3, 3, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_1374916 : Nat := 118140960795 + 1374916 * 2 ^ 59
def prefixEnd_1374916 : Nat := 4983230072969 + 3 ^ 40 * 1374916 * 2
def baseEnd_1374916 : Nat := 705992767557247868526883

theorem tailTrace_1374916 : CollatzResearch.WordTrace tailWord_1374916 prefixEnd_1374916 705992767557247868526883 := by
  unfold tailWord_1374916
  simp only [CollatzResearch.WordTrace]
  refine ⟨25073653143460811901588301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33431537524614415868784401 25073653143460811901588301)
  ·
    refine ⟨9402619928797804463095613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25073653143460811901588301 9402619928797804463095613)
    ·
      refine ⟨3525982473299176673660855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9402619928797804463095613 3525982473299176673660855)
      ·
        refine ⟨5288973709948765010491283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3525982473299176673660855 5288973709948765010491283)
        ·
          refine ⟨7933460564923147515736925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288973709948765010491283 7933460564923147515736925)
          ·
            refine ⟨2975047711846180318401347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7933460564923147515736925 2975047711846180318401347)
            ·
              refine ⟨4462571567769270477602021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975047711846180318401347 4462571567769270477602021)
              ·
                refine ⟨836732168956738214550379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4462571567769270477602021 836732168956738214550379)
                ·
                  refine ⟨1255098253435107321825569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836732168956738214550379 1255098253435107321825569)
                  ·
                    refine ⟨941323690076330491369177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1255098253435107321825569 941323690076330491369177)
                    ·
                      refine ⟨705992767557247868526883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941323690076330491369177 705992767557247868526883)
                      ·
                        rfl

theorem cell23_1374916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_1374916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374916 prefixEnd_1374916 := by exact prefixLift 1374916
  have htrace : WordTrace (prefixWord ++ tailWord_1374916) baseStart_1374916 baseEnd_1374916 := by
    simpa [prefixWord, tailWord_1374916, baseEnd_1374916] using wordTrace_append hprefix tailTrace_1374916
  have hstable : (prefixWord ++ tailWord_1374916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374916).length < 2 ^ (prefixWord ++ tailWord_1374916).sum := by decide
  have hdescent : baseEnd_1374916 < baseStart_1374916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374938 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1374938 : Nat := 118140960795 + 1374938 * 2 ^ 59
def prefixEnd_1374938 : Nat := 4983230072969 + 3 ^ 40 * 1374938 * 2
def baseEnd_1374938 : Nat := 706004064131646782451781

theorem tailTrace_1374938 : CollatzResearch.WordTrace tailWord_1374938 prefixEnd_1374938 706004064131646782451781 := by
  unfold tailWord_1374938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12537027173210480390119367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33432072461894614373651645 12537027173210480390119367)
  ·
    refine ⟨18805540759815720585179051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12537027173210480390119367 18805540759815720585179051)
    ·
      refine ⟨28208311139723580877768577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18805540759815720585179051 28208311139723580877768577)
      ·
        refine ⟨21156233354792685658326433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28208311139723580877768577 21156233354792685658326433)
        ·
          refine ⟨15867175016094514243744825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21156233354792685658326433 15867175016094514243744825)
          ·
            refine ⟨11900381262070885682808619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15867175016094514243744825 11900381262070885682808619)
            ·
              refine ⟨17850571893106328524212929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11900381262070885682808619 17850571893106328524212929)
              ·
                refine ⟨13387928919829746393159697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17850571893106328524212929 13387928919829746393159697)
                ·
                  refine ⟨10040946689872309794869773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13387928919829746393159697 10040946689872309794869773)
                  ·
                    refine ⟨3765355008702116173076165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10040946689872309794869773 3765355008702116173076165)
                    ·
                      refine ⟨706004064131646782451781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3765355008702116173076165 706004064131646782451781)
                      ·
                        rfl

theorem cell23_1374938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1374938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374938 prefixEnd_1374938 := by exact prefixLift 1374938
  have htrace : WordTrace (prefixWord ++ tailWord_1374938) baseStart_1374938 baseEnd_1374938 := by
    simpa [prefixWord, tailWord_1374938, baseEnd_1374938] using wordTrace_append hprefix tailTrace_1374938
  have hstable : (prefixWord ++ tailWord_1374938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374938).length < 2 ^ (prefixWord ++ tailWord_1374938).sum := by decide
  have hdescent : baseEnd_1374938 < baseStart_1374938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374959 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 1, 3, 2]
def baseStart_1374959 : Nat := 118140960795 + 1374959 * 2 ^ 59
def prefixEnd_1374959 : Nat := 4983230072969 + 3 ^ 40 * 1374959 * 2
def baseEnd_1374959 : Nat := 706014847225391200289185

theorem tailTrace_1374959 : CollatzResearch.WordTrace tailWord_1374959 prefixEnd_1374959 706014847225391200289185 := by
  unfold tailWord_1374959
  simp only [CollatzResearch.WordTrace]
  refine ⟨50148874625765842146991931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33432583083843894764661287 50148874625765842146991931)
  ·
    refine ⟨75223311938648763220487897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50148874625765842146991931 75223311938648763220487897)
    ·
      refine ⟨56417483953986572415365923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75223311938648763220487897 56417483953986572415365923)
      ·
        refine ⟨84626225930979858623048885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56417483953986572415365923 84626225930979858623048885)
        ·
          refine ⟨7933708681029361745910833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84626225930979858623048885 7933708681029361745910833)
          ·
            refine ⟨5950281510772021309433125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7933708681029361745910833 5950281510772021309433125)
            ·
              refine ⟨1115677783269753995518711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5950281510772021309433125 1115677783269753995518711)
              ·
                refine ⟨1673516674904630993278067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115677783269753995518711 1673516674904630993278067)
                ·
                  refine ⟨2510275012356946489917101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673516674904630993278067 2510275012356946489917101)
                  ·
                    refine ⟨941353129633854933718913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2510275012356946489917101 941353129633854933718913)
                    ·
                      refine ⟨706014847225391200289185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941353129633854933718913 706014847225391200289185)
                      ·
                        rfl

theorem cell23_1374959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 3, 2].length) (baseStart_1374959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374959 prefixEnd_1374959 := by exact prefixLift 1374959
  have htrace : WordTrace (prefixWord ++ tailWord_1374959) baseStart_1374959 baseEnd_1374959 := by
    simpa [prefixWord, tailWord_1374959, baseEnd_1374959] using wordTrace_append hprefix tailTrace_1374959
  have hstable : (prefixWord ++ tailWord_1374959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374959).length < 2 ^ (prefixWord ++ tailWord_1374959).sum := by decide
  have hdescent : baseEnd_1374959 < baseStart_1374959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374968 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_1374968 : Nat := 118140960795 + 1374968 * 2 ^ 59
def prefixEnd_1374968 : Nat := 4983230072969 + 3 ^ 40 * 1374968 * 2
def baseEnd_1374968 : Nat := 706019468551281665076643

theorem tailTrace_1374968 : CollatzResearch.WordTrace tailWord_1374968 prefixEnd_1374968 706019468551281665076643 := by
  unfold tailWord_1374968
  simp only [CollatzResearch.WordTrace]
  refine ⟨25074601441366618342034779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33432801921822157789379705 25074601441366618342034779)
  ·
    refine ⟨37611902162049927513052169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25074601441366618342034779 37611902162049927513052169)
    ·
      refine ⟨28208926621537445634789127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37611902162049927513052169 28208926621537445634789127)
      ·
        refine ⟨42313389932306168452183691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28208926621537445634789127 42313389932306168452183691)
        ·
          refine ⟨63470084898459252678275537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42313389932306168452183691 63470084898459252678275537)
          ·
            refine ⟨47602563673844439508706653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63470084898459252678275537 47602563673844439508706653)
            ·
              refine ⟨17850961377691664815764995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47602563673844439508706653 17850961377691664815764995)
              ·
                refine ⟨26776442066537497223647493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17850961377691664815764995 26776442066537497223647493)
                ·
                  refine ⟨5020582887475780729433905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26776442066537497223647493 5020582887475780729433905)
                  ·
                    refine ⟨3765437165606835547075429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020582887475780729433905 3765437165606835547075429)
                    ·
                      refine ⟨706019468551281665076643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3765437165606835547075429 706019468551281665076643)
                      ·
                        rfl

theorem cell23_1374968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_1374968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1374968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1374968 prefixEnd_1374968 := by exact prefixLift 1374968
  have htrace : WordTrace (prefixWord ++ tailWord_1374968) baseStart_1374968 baseEnd_1374968 := by
    simpa [prefixWord, tailWord_1374968, baseEnd_1374968] using wordTrace_append hprefix tailTrace_1374968
  have hstable : (prefixWord ++ tailWord_1374968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374968).length < 2 ^ (prefixWord ++ tailWord_1374968).sum := by decide
  have hdescent : baseEnd_1374968 < baseStart_1374968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375025 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 2, 5]
def baseStart_1375025 : Nat := 118140960795 + 1375025 * 2 ^ 59
def prefixEnd_1375025 : Nat := 4983230072969 + 3 ^ 40 * 1375025 * 2
def baseEnd_1375025 : Nat := 235349578982862647354627

theorem tailTrace_1375025 : CollatzResearch.WordTrace tailWord_1375025 prefixEnd_1375025 235349578982862647354627 := by
  unfold tailWord_1375025
  simp only [CollatzResearch.WordTrace]
  refine ⟨50151281843526735418894529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33434187895684490279263019 50151281843526735418894529)
  ·
    refine ⟨37613461382645051564170897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50151281843526735418894529 37613461382645051564170897)
    ·
      refine ⟨28210096036983788673128173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37613461382645051564170897 28210096036983788673128173)
      ·
        refine ⟨10578786013868920752423065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28210096036983788673128173 10578786013868920752423065)
        ·
          refine ⟨7934089510401690564317299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10578786013868920752423065 7934089510401690564317299)
          ·
            refine ⟨11901134265602535846475949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7934089510401690564317299 11901134265602535846475949)
            ·
              refine ⟨4462925349600950942428481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11901134265602535846475949 4462925349600950942428481)
              ·
                refine ⟨3347194012200713206821361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4462925349600950942428481 3347194012200713206821361)
                ·
                  refine ⟨2510395509150534905116021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3347194012200713206821361 2510395509150534905116021)
                  ·
                    refine ⟨235349578982862647354627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2510395509150534905116021 235349578982862647354627)
                    ·
                      rfl

theorem cell23_1375025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_1375025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375025 prefixEnd_1375025 := by exact prefixLift 1375025
  have htrace : WordTrace (prefixWord ++ tailWord_1375025) baseStart_1375025 baseEnd_1375025 := by
    simpa [prefixWord, tailWord_1375025, baseEnd_1375025] using wordTrace_append hprefix tailTrace_1375025
  have hstable : (prefixWord ++ tailWord_1375025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375025).length < 2 ^ (prefixWord ++ tailWord_1375025).sum := by decide
  have hdescent : baseEnd_1375025 < baseStart_1375025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375029 : List Nat := [1, 3, 3, 1, 3, 2, 3, 2, 5]
def baseStart_1375029 : Nat := 118140960795 + 1375029 * 2 ^ 59
def prefixEnd_1375029 : Nat := 4983230072969 + 3 ^ 40 * 1375029 * 2
def baseEnd_1375029 : Nat := 78450087874578436268207

theorem tailTrace_1375029 : CollatzResearch.WordTrace tailWord_1375029 prefixEnd_1375029 78450087874578436268207 := by
  unfold tailWord_1375029
  simp only [CollatzResearch.WordTrace]
  refine ⟨50151427735512244102040141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33434285157008162734693427 50151427735512244102040141)
  ·
    refine ⟨18806785400817091538265053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50151427735512244102040141 18806785400817091538265053)
    ·
      refine ⟨7052544525306409326849395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18806785400817091538265053 7052544525306409326849395)
      ·
        refine ⟨10578816787959613990274093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7052544525306409326849395 10578816787959613990274093)
        ·
          refine ⟨3967056295484855246352785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10578816787959613990274093 3967056295484855246352785)
          ·
            refine ⟨2975292221613641434764589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3967056295484855246352785 2975292221613641434764589)
            ·
              refine ⟨1115734583105115538036721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2975292221613641434764589 1115734583105115538036721)
              ·
                refine ⟨836800937328836653527541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115734583105115538036721 836800937328836653527541)
                ·
                  refine ⟨78450087874578436268207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 836800937328836653527541 78450087874578436268207)
                  ·
                    rfl

theorem cell23_1375029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_1375029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375029 prefixEnd_1375029 := by exact prefixLift 1375029
  have htrace : WordTrace (prefixWord ++ tailWord_1375029) baseStart_1375029 baseEnd_1375029 := by
    simpa [prefixWord, tailWord_1375029, baseEnd_1375029] using wordTrace_append hprefix tailTrace_1375029
  have hstable : (prefixWord ++ tailWord_1375029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375029).length < 2 ^ (prefixWord ++ tailWord_1375029).sum := by decide
  have hdescent : baseEnd_1375029 < baseStart_1375029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375089 : List Nat := [1, 2, 2, 2, 1, 5, 1, 4, 1, 4]
def baseStart_1375089 : Nat := 118140960795 + 1375089 * 2 ^ 59
def prefixEnd_1375089 : Nat := 4983230072969 + 3 ^ 40 * 1375089 * 2
def baseEnd_1375089 : Nat := 235360533236825230554529

theorem tailTrace_1375089 : CollatzResearch.WordTrace tailWord_1375089 prefixEnd_1375089 235360533236825230554529 := by
  unfold tailWord_1375089
  simp only [CollatzResearch.WordTrace]
  refine ⟨50153616115294874349224321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33435744076863249566149547 50153616115294874349224321)
  ·
    refine ⟨37615212086471155761918241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50153616115294874349224321 37615212086471155761918241)
    ·
      refine ⟨28211409064853366821438681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37615212086471155761918241 28211409064853366821438681)
      ·
        refine ⟨21158556798640025116079011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28211409064853366821438681 21158556798640025116079011)
        ·
          refine ⟨31737835197960037674118517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21158556798640025116079011 31737835197960037674118517)
          ·
            refine ⟨2975422049808753531948611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31737835197960037674118517 2975422049808753531948611)
            ·
              refine ⟨4463133074713130297922917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975422049808753531948611 4463133074713130297922917)
              ·
                refine ⟨836837451508711930860547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4463133074713130297922917 836837451508711930860547)
                ·
                  refine ⟨1255256177263067896290821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836837451508711930860547 1255256177263067896290821)
                  ·
                    refine ⟨235360533236825230554529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1255256177263067896290821 235360533236825230554529)
                    ·
                      rfl

theorem cell23_1375089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_1375089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375089 prefixEnd_1375089 := by exact prefixLift 1375089
  have htrace : WordTrace (prefixWord ++ tailWord_1375089) baseStart_1375089 baseEnd_1375089 := by
    simpa [prefixWord, tailWord_1375089, baseEnd_1375089] using wordTrace_append hprefix tailTrace_1375089
  have hstable : (prefixWord ++ tailWord_1375089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375089).length < 2 ^ (prefixWord ++ tailWord_1375089).sum := by decide
  have hdescent : baseEnd_1375089 < baseStart_1375089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375115 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 3, 5]
def baseStart_1375115 : Nat := 118140960795 + 1375115 * 2 ^ 59
def prefixEnd_1375115 : Nat := 4983230072969 + 3 ^ 40 * 1375115 * 2
def baseEnd_1375115 : Nat := 235364983402497529979489

theorem tailTrace_1375115 : CollatzResearch.WordTrace tailWord_1375115 prefixEnd_1375115 235364983402497529979489 := by
  unfold tailWord_1375115
  simp only [CollatzResearch.WordTrace]
  refine ⟨50154564413200680789670799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33436376275467120526447199 50154564413200680789670799)
  ·
    refine ⟨75231846619801021184506199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50154564413200680789670799 75231846619801021184506199)
    ·
      refine ⟨112847769929701531776759299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75231846619801021184506199 112847769929701531776759299)
      ·
        refine ⟨169271654894552297665138949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112847769929701531776759299 169271654894552297665138949)
        ·
          refine ⟨31738435292728555812213553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169271654894552297665138949 31738435292728555812213553)
          ·
            refine ⟨23803826469546416859160165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31738435292728555812213553 23803826469546416859160165)
            ·
              refine ⟨4463217463039953161092531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23803826469546416859160165 4463217463039953161092531)
              ·
                refine ⟨6694826194559929741638797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463217463039953161092531 6694826194559929741638797)
                ·
                  refine ⟨2510559822959973653114549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6694826194559929741638797 2510559822959973653114549)
                  ·
                    refine ⟨235364983402497529979489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2510559822959973653114549 235364983402497529979489)
                    ·
                      rfl

theorem cell23_1375115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 5].length) (baseStart_1375115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375115 prefixEnd_1375115 := by exact prefixLift 1375115
  have htrace : WordTrace (prefixWord ++ tailWord_1375115) baseStart_1375115 baseEnd_1375115 := by
    simpa [prefixWord, tailWord_1375115, baseEnd_1375115] using wordTrace_append hprefix tailTrace_1375115
  have hstable : (prefixWord ++ tailWord_1375115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375115).length < 2 ^ (prefixWord ++ tailWord_1375115).sum := by decide
  have hdescent : baseEnd_1375115 < baseStart_1375115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375155 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 3]
def baseStart_1375155 : Nat := 118140960795 + 1375155 * 2 ^ 59
def prefixEnd_1375155 : Nat := 4983230072969 + 3 ^ 40 * 1375155 * 2
def baseEnd_1375155 : Nat := 706115489433672433438283

theorem tailTrace_1375155 : CollatzResearch.WordTrace tailWord_1375155 prefixEnd_1375155 706115489433672433438283 := by
  unfold tailWord_1375155
  simp only [CollatzResearch.WordTrace]
  refine ⟨50156023333055767621126919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33437348888703845080751279 50156023333055767621126919)
  ·
    refine ⟨75234034999583651431690379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50156023333055767621126919 75234034999583651431690379)
    ·
      refine ⟨112851052499375477147535569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75234034999583651431690379 112851052499375477147535569)
      ·
        refine ⟨84638289374531607860651677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112851052499375477147535569 84638289374531607860651677)
        ·
          refine ⟨31739358515449352947744379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84638289374531607860651677 31739358515449352947744379)
          ·
            refine ⟨47609037773174029421616569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31739358515449352947744379 47609037773174029421616569)
            ·
              refine ⟨35706778329880522066212427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47609037773174029421616569 35706778329880522066212427)
              ·
                refine ⟨53560167494820783099318641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35706778329880522066212427 53560167494820783099318641)
                ·
                  refine ⟨40170125621115587324488981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53560167494820783099318641 40170125621115587324488981)
                  ·
                    refine ⟨1882974638489793155835421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40170125621115587324488981 1882974638489793155835421)
                    ·
                      refine ⟨706115489433672433438283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1882974638489793155835421 706115489433672433438283)
                      ·
                        rfl

theorem cell23_1375155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_1375155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375155 prefixEnd_1375155 := by exact prefixLift 1375155
  have htrace : WordTrace (prefixWord ++ tailWord_1375155) baseStart_1375155 baseEnd_1375155 := by
    simpa [prefixWord, tailWord_1375155, baseEnd_1375155] using wordTrace_append hprefix tailTrace_1375155
  have hstable : (prefixWord ++ tailWord_1375155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375155).length < 2 ^ (prefixWord ++ tailWord_1375155).sum := by decide
  have hdescent : baseEnd_1375155 < baseStart_1375155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375156 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_1375156 : Nat := 118140960795 + 1375156 * 2 ^ 59
def prefixEnd_1375156 : Nat := 4983230072969 + 3 ^ 40 * 1375156 * 2
def baseEnd_1375156 : Nat := 706116002914326929525779

theorem tailTrace_1375156 : CollatzResearch.WordTrace tailWord_1375156 prefixEnd_1375156 706116002914326929525779 := by
  unfold tailWord_1375156
  simp only [CollatzResearch.WordTrace]
  refine ⟨25078029903026072395956661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33437373204034763194608881 25078029903026072395956661)
  ·
    refine ⟨2351065303408694287120937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25078029903026072395956661 2351065303408694287120937)
    ·
      refine ⟨1763298977556520715340703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2351065303408694287120937 1763298977556520715340703)
      ·
        refine ⟨2644948466334781073011055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763298977556520715340703 2644948466334781073011055)
        ·
          refine ⟨3967422699502171609516583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644948466334781073011055 3967422699502171609516583)
          ·
            refine ⟨5951134049253257414274875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967422699502171609516583 5951134049253257414274875)
            ·
              refine ⟨8926701073879886121412313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5951134049253257414274875 8926701073879886121412313)
              ·
                refine ⟨6695025805409914591059235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8926701073879886121412313 6695025805409914591059235)
                ·
                  refine ⟨10042538708114871886588853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6695025805409914591059235 10042538708114871886588853)
                  ·
                    refine ⟨941488003885769239367705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10042538708114871886588853 941488003885769239367705)
                    ·
                      refine ⟨706116002914326929525779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941488003885769239367705 706116002914326929525779)
                      ·
                        rfl

theorem cell23_1375156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_1375156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375156 prefixEnd_1375156 := by exact prefixLift 1375156
  have htrace : WordTrace (prefixWord ++ tailWord_1375156) baseStart_1375156 baseEnd_1375156 := by
    simpa [prefixWord, tailWord_1375156, baseEnd_1375156] using wordTrace_append hprefix tailTrace_1375156
  have hstable : (prefixWord ++ tailWord_1375156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375156).length < 2 ^ (prefixWord ++ tailWord_1375156).sum := by decide
  have hdescent : baseEnd_1375156 < baseStart_1375156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375174 : List Nat := [6, 1, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1375174 : Nat := 118140960795 + 1375174 * 2 ^ 59
def prefixEnd_1375174 : Nat := 4983230072969 + 3 ^ 40 * 1375174 * 2
def baseEnd_1375174 : Nat := 235375081855369286366899

theorem tailTrace_1375174 : CollatzResearch.WordTrace tailWord_1375174 prefixEnd_1375174 235375081855369286366899 := by
  unfold tailWord_1375174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567397384999591683314643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33437810879991289244045717 1567397384999591683314643)
  ·
    refine ⟨2351096077499387524971965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1567397384999591683314643 2351096077499387524971965)
    ·
      refine ⟨881661029062270321864487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2351096077499387524971965 881661029062270321864487)
      ·
        refine ⟨1322491543593405482796731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881661029062270321864487 1322491543593405482796731)
        ·
          refine ⟨1983737315390108224195097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322491543593405482796731 1983737315390108224195097)
          ·
            refine ⟨1487802986542581168146323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1983737315390108224195097 1487802986542581168146323)
            ·
              refine ⟨2231704479813871752219485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487802986542581168146323 2231704479813871752219485)
              ·
                refine ⟨836889179930201907082307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2231704479813871752219485 836889179930201907082307)
                ·
                  refine ⟨1255333769895302860623461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836889179930201907082307 1255333769895302860623461)
                  ·
                    refine ⟨235375081855369286366899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1255333769895302860623461 235375081855369286366899)
                    ·
                      rfl

theorem cell23_1375174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1375174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375174 prefixEnd_1375174 := by exact prefixLift 1375174
  have htrace : WordTrace (prefixWord ++ tailWord_1375174) baseStart_1375174 baseEnd_1375174 := by
    simpa [prefixWord, tailWord_1375174, baseEnd_1375174] using wordTrace_append hprefix tailTrace_1375174
  have hstable : (prefixWord ++ tailWord_1375174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375174).length < 2 ^ (prefixWord ++ tailWord_1375174).sum := by decide
  have hdescent : baseEnd_1375174 < baseStart_1375174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375189 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1375189 : Nat := 118140960795 + 1375189 * 2 ^ 59
def prefixEnd_1375189 : Nat := 4983230072969 + 3 ^ 40 * 1375189 * 2
def baseEnd_1375189 : Nat := 706132947775925300413127

theorem tailTrace_1375189 : CollatzResearch.WordTrace tailWord_1375189 prefixEnd_1375189 706132947775925300413127 := by
  unfold tailWord_1375189
  simp only [CollatzResearch.WordTrace]
  refine ⟨50157263414932591427864621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33438175609955060951909747 50157263414932591427864621)
  ·
    refine ⟨18808973780599721785449233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50157263414932591427864621 18808973780599721785449233)
    ·
      refine ⟨14106730335449791339086925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18808973780599721785449233 14106730335449791339086925)
      ·
        refine ⟨5290023875793671752157597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14106730335449791339086925 5290023875793671752157597)
        ·
          refine ⟨1983758953422626907059099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5290023875793671752157597 1983758953422626907059099)
          ·
            refine ⟨2975638430133940360588649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983758953422626907059099 2975638430133940360588649)
            ·
              refine ⟨2231728822600455270441487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2975638430133940360588649 2231728822600455270441487)
              ·
                refine ⟨3347593233900682905662231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231728822600455270441487 3347593233900682905662231)
                ·
                  refine ⟨5021389850851024358493347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347593233900682905662231 5021389850851024358493347)
                  ·
                    refine ⟨7532084776276536537740021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5021389850851024358493347 7532084776276536537740021)
                    ·
                      refine ⟨706132947775925300413127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7532084776276536537740021 706132947775925300413127)
                      ·
                        rfl

theorem cell23_1375189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1375189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375189 prefixEnd_1375189 := by exact prefixLift 1375189
  have htrace : WordTrace (prefixWord ++ tailWord_1375189) baseStart_1375189 baseEnd_1375189 := by
    simpa [prefixWord, tailWord_1375189, baseEnd_1375189] using wordTrace_append hprefix tailTrace_1375189
  have hstable : (prefixWord ++ tailWord_1375189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375189).length < 2 ^ (prefixWord ++ tailWord_1375189).sum := by decide
  have hdescent : baseEnd_1375189 < baseStart_1375189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375212 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 9, 2]
def baseStart_1375212 : Nat := 118140960795 + 1375212 * 2 ^ 59
def prefixEnd_1375212 : Nat := 4983230072969 + 3 ^ 40 * 1375212 * 2
def baseEnd_1375212 : Nat := 706144757830978710425521

theorem tailTrace_1375212 : CollatzResearch.WordTrace tailWord_1375212 prefixEnd_1375212 706144757830978710425521 := by
  unfold tailWord_1375212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25079051146924633177975945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33438734862566177570634593 25079051146924633177975945)
  ·
    refine ⟨18809288360193474883481959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25079051146924633177975945 18809288360193474883481959)
    ·
      refine ⟨28213932540290212325222939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18809288360193474883481959 28213932540290212325222939)
      ·
        refine ⟨42320898810435318487834409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28213932540290212325222939 42320898810435318487834409)
        ·
          refine ⟨31740674107826488865875807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42320898810435318487834409 31740674107826488865875807)
          ·
            refine ⟨47611011161739733298813711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31740674107826488865875807 47611011161739733298813711)
            ·
              refine ⟨71416516742609599948220567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47611011161739733298813711 71416516742609599948220567)
              ·
                refine ⟨107124775113914399922330851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71416516742609599948220567 107124775113914399922330851)
                ·
                  refine ⟨160687162670871599883496277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107124775113914399922330851 160687162670871599883496277)
                  ·
                    refine ⟨941526343774638280567361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 160687162670871599883496277 941526343774638280567361)
                    ·
                      refine ⟨706144757830978710425521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941526343774638280567361 706144757830978710425521)
                      ·
                        rfl

theorem cell23_1375212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_1375212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375212 prefixEnd_1375212 := by exact prefixLift 1375212
  have htrace : WordTrace (prefixWord ++ tailWord_1375212) baseStart_1375212 baseEnd_1375212 := by
    simpa [prefixWord, tailWord_1375212, baseEnd_1375212] using wordTrace_append hprefix tailTrace_1375212
  have hstable : (prefixWord ++ tailWord_1375212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375212).length < 2 ^ (prefixWord ++ tailWord_1375212).sum := by decide
  have hdescent : baseEnd_1375212 < baseStart_1375212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375220 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1375220 : Nat := 118140960795 + 1375220 * 2 ^ 59
def prefixEnd_1375220 : Nat := 4983230072969 + 3 ^ 40 * 1375220 * 2
def baseEnd_1375220 : Nat := 706148865676214679125485

theorem tailTrace_1375220 : CollatzResearch.WordTrace tailWord_1375220 prefixEnd_1375220 706148865676214679125485 := by
  unfold tailWord_1375220
  simp only [CollatzResearch.WordTrace]
  refine ⟨25079197038910141861121557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33438929385213522481495409 25079197038910141861121557)
  ·
    refine ⟨1175587361198912899740073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25079197038910141861121557 1175587361198912899740073)
    ·
      refine ⟨881690520899184674805055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1175587361198912899740073 881690520899184674805055)
      ·
        refine ⟨1322535781348777012207583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881690520899184674805055 1322535781348777012207583)
        ·
          refine ⟨1983803672023165518311375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322535781348777012207583 1983803672023165518311375)
          ·
            refine ⟨2975705508034748277467063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983803672023165518311375 2975705508034748277467063)
            ·
              refine ⟨4463558262052122416200595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975705508034748277467063 4463558262052122416200595)
              ·
                refine ⟨6695337393078183624300893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463558262052122416200595 6695337393078183624300893)
                ·
                  refine ⟨2510751522404318859112835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6695337393078183624300893 2510751522404318859112835)
                  ·
                    refine ⟨3766127283606478288669253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2510751522404318859112835 3766127283606478288669253)
                    ·
                      refine ⟨706148865676214679125485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3766127283606478288669253 706148865676214679125485)
                      ·
                        rfl

theorem cell23_1375220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1375220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375220 prefixEnd_1375220 := by exact prefixLift 1375220
  have htrace : WordTrace (prefixWord ++ tailWord_1375220) baseStart_1375220 baseEnd_1375220 := by
    simpa [prefixWord, tailWord_1375220, baseEnd_1375220] using wordTrace_append hprefix tailTrace_1375220
  have hstable : (prefixWord ++ tailWord_1375220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375220).length < 2 ^ (prefixWord ++ tailWord_1375220).sum := by decide
  have hdescent : baseEnd_1375220 < baseStart_1375220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375235 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 6, 6]
def baseStart_1375235 : Nat := 118140960795 + 1375235 * 2 ^ 59
def prefixEnd_1375235 : Nat := 4983230072969 + 3 ^ 40 * 1375235 * 2
def baseEnd_1375235 : Nat := 235385522628677373479305

theorem tailTrace_1375235 : CollatzResearch.WordTrace tailWord_1375235 prefixEnd_1375235 235385522628677373479305 := by
  unfold tailWord_1375235
  simp only [CollatzResearch.WordTrace]
  refine ⟨50158941172765941284039159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33439294115177294189359439 50158941172765941284039159)
  ·
    refine ⟨75238411759148911926058739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50158941172765941284039159 75238411759148911926058739)
    ·
      refine ⟨112857617638723367889088109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75238411759148911926058739 112857617638723367889088109)
      ·
        refine ⟨42321606614521262958408041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112857617638723367889088109 42321606614521262958408041)
        ·
          refine ⟨31741204960890947218806031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42321606614521262958408041 31741204960890947218806031)
          ·
            refine ⟨47611807441336420828209047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31741204960890947218806031 47611807441336420828209047)
            ·
              refine ⟨71417711162004631242313571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47611807441336420828209047 71417711162004631242313571)
              ·
                refine ⟨107126566743006946863470357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71417711162004631242313571 107126566743006946863470357)
                ·
                  refine ⟨5021557816078450634225173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107126566743006946863470357 5021557816078450634225173)
                  ·
                    refine ⟨235385522628677373479305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5021557816078450634225173 235385522628677373479305)
                    ·
                      rfl

theorem cell23_1375235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 6].length) (baseStart_1375235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375235 prefixEnd_1375235 := by exact prefixLift 1375235
  have htrace : WordTrace (prefixWord ++ tailWord_1375235) baseStart_1375235 baseEnd_1375235 := by
    simpa [prefixWord, tailWord_1375235, baseEnd_1375235] using wordTrace_append hprefix tailTrace_1375235
  have hstable : (prefixWord ++ tailWord_1375235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375235).length < 2 ^ (prefixWord ++ tailWord_1375235).sum := by decide
  have hdescent : baseEnd_1375235 < baseStart_1375235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375259 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 8, 2, 2]
def baseStart_1375259 : Nat := 118140960795 + 1375259 * 2 ^ 59
def prefixEnd_1375259 : Nat := 4983230072969 + 3 ^ 40 * 1375259 * 2
def baseEnd_1375259 : Nat := 706168891421740026537805

theorem tailTrace_1375259 : CollatzResearch.WordTrace tailWord_1375259 prefixEnd_1375259 706168891421740026537805 := by
  unfold tailWord_1375259
  simp only [CollatzResearch.WordTrace]
  refine ⟨50159816524678993382912831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33439877683119328921941887 50159816524678993382912831)
  ·
    refine ⟨75239724787018490074369247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50159816524678993382912831 75239724787018490074369247)
    ·
      refine ⟨112859587180527735111553871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75239724787018490074369247 112859587180527735111553871)
      ·
        refine ⟨169289380770791602667330807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112859587180527735111553871 169289380770791602667330807)
        ·
          refine ⟨253934071156187404000996211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169289380770791602667330807 253934071156187404000996211)
          ·
            refine ⟨380901106734281106001494317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253934071156187404000996211 380901106734281106001494317)
            ·
              refine ⟨142837915025355414750560369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380901106734281106001494317 142837915025355414750560369)
              ·
                refine ⟨107128436269016561062920277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142837915025355414750560369 107128436269016561062920277)
                ·
                  refine ⟨1255411362527537824956097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 107128436269016561062920277 1255411362527537824956097)
                  ·
                    refine ⟨941558521895653368717073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1255411362527537824956097 941558521895653368717073)
                    ·
                      refine ⟨706168891421740026537805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941558521895653368717073 706168891421740026537805)
                      ·
                        rfl

theorem cell23_1375259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 2, 2].length) (baseStart_1375259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375259 prefixEnd_1375259 := by exact prefixLift 1375259
  have htrace : WordTrace (prefixWord ++ tailWord_1375259) baseStart_1375259 baseEnd_1375259 := by
    simpa [prefixWord, tailWord_1375259, baseEnd_1375259] using wordTrace_append hprefix tailTrace_1375259
  have hstable : (prefixWord ++ tailWord_1375259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375259).length < 2 ^ (prefixWord ++ tailWord_1375259).sum := by decide
  have hdescent : baseEnd_1375259 < baseStart_1375259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375276 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 2, 2, 2]
def baseStart_1375276 : Nat := 118140960795 + 1375276 * 2 ^ 59
def prefixEnd_1375276 : Nat := 4983230072969 + 3 ^ 40 * 1375276 * 2
def baseEnd_1375276 : Nat := 706177620592866460025227

theorem tailTrace_1375276 : CollatzResearch.WordTrace tailWord_1375276 prefixEnd_1375276 706177620592866460025227 := by
  unfold tailWord_1375276
  simp only [CollatzResearch.WordTrace]
  refine ⟨25080218282808702643140841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33440291043744936857521121 25080218282808702643140841)
  ·
    refine ⟨18810163712106526982355631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25080218282808702643140841 18810163712106526982355631)
    ·
      refine ⟨28215245568159790473533447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18810163712106526982355631 28215245568159790473533447)
      ·
        refine ⟨42322868352239685710300171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28215245568159790473533447 42322868352239685710300171)
        ·
          refine ⟨63484302528359528565450257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42322868352239685710300171 63484302528359528565450257)
          ·
            refine ⟨47613226896269646424087693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63484302528359528565450257 47613226896269646424087693)
            ·
              refine ⟨17854960086101117409032885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47613226896269646424087693 17854960086101117409032885)
              ·
                refine ⟨1673902508071979757096833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17854960086101117409032885 1673902508071979757096833)
                ·
                  refine ⟨1255426881053984817822625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1673902508071979757096833 1255426881053984817822625)
                  ·
                    refine ⟨941570160790488613366969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1255426881053984817822625 941570160790488613366969)
                    ·
                      refine ⟨706177620592866460025227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941570160790488613366969 706177620592866460025227)
                      ·
                        rfl

theorem cell23_1375276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_1375276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375276 prefixEnd_1375276 := by exact prefixLift 1375276
  have htrace : WordTrace (prefixWord ++ tailWord_1375276) baseStart_1375276 baseEnd_1375276 := by
    simpa [prefixWord, tailWord_1375276, baseEnd_1375276] using wordTrace_append hprefix tailTrace_1375276
  have hstable : (prefixWord ++ tailWord_1375276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375276).length < 2 ^ (prefixWord ++ tailWord_1375276).sum := by decide
  have hdescent : baseEnd_1375276 < baseStart_1375276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375282 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 7]
def baseStart_1375282 : Nat := 118140960795 + 1375282 * 2 ^ 59
def prefixEnd_1375282 : Nat := 4983230072969 + 3 ^ 40 * 1375282 * 2
def baseEnd_1375282 : Nat := 78464522386310381838911

theorem tailTrace_1375282 : CollatzResearch.WordTrace tailWord_1375282 prefixEnd_1375282 78464522386310381838911 := by
  unfold tailWord_1375282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12540163850898917077750025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33440436935730445540666733 12540163850898917077750025)
  ·
    refine ⟨9405122888174187808312519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12540163850898917077750025 9405122888174187808312519)
    ·
      refine ⟨14107684332261281712468779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9405122888174187808312519 14107684332261281712468779)
      ·
        refine ⟨21161526498391922568703169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14107684332261281712468779 21161526498391922568703169)
        ·
          refine ⟨15871144873793941926527377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21161526498391922568703169 15871144873793941926527377)
          ·
            refine ⟨11903358655345456444895533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15871144873793941926527377 11903358655345456444895533)
            ·
              refine ⟨4463759495754546166835825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11903358655345456444895533 4463759495754546166835825)
              ·
                refine ⟨3347819621815909625126869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4463759495754546166835825 3347819621815909625126869)
                ·
                  refine ⟨78464522386310381838911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3347819621815909625126869 78464522386310381838911)
                  ·
                    rfl

theorem cell23_1375282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_1375282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375282 prefixEnd_1375282 := by exact prefixLift 1375282
  have htrace : WordTrace (prefixWord ++ tailWord_1375282) baseStart_1375282 baseEnd_1375282 := by
    simpa [prefixWord, tailWord_1375282, baseEnd_1375282] using wordTrace_append hprefix tailTrace_1375282
  have hstable : (prefixWord ++ tailWord_1375282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375282).length < 2 ^ (prefixWord ++ tailWord_1375282).sum := by decide
  have hdescent : baseEnd_1375282 < baseStart_1375282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375297 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_1375297 : Nat := 118140960795 + 1375297 * 2 ^ 59
def prefixEnd_1375297 : Nat := 4983230072969 + 3 ^ 40 * 1375297 * 2
def baseEnd_1375297 : Nat := 706188403686610877862631

theorem tailTrace_1375297 : CollatzResearch.WordTrace tailWord_1375297 prefixEnd_1375297 706188403686610877862631 := by
  unfold tailWord_1375297
  simp only [CollatzResearch.WordTrace]
  refine ⟨50161202498541325872796145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33440801665694217248530763 50161202498541325872796145)
  ·
    refine ⟨37620901873905994404597109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50161202498541325872796145 37620901873905994404597109)
    ·
      refine ⟨3526959550678686975430979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37620901873905994404597109 3526959550678686975430979)
      ·
        refine ⟨5290439326018030463146469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3526959550678686975430979 5290439326018030463146469)
        ·
          refine ⟨991957373628380711839963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5290439326018030463146469 991957373628380711839963)
          ·
            refine ⟨1487936060442571067759945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991957373628380711839963 1487936060442571067759945)
            ·
              refine ⟨1115952045331928300819959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487936060442571067759945 1115952045331928300819959)
              ·
                refine ⟨1673928067997892451229939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115952045331928300819959 1673928067997892451229939)
                ·
                  refine ⟨2510892101996838676844909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673928067997892451229939 2510892101996838676844909)
                  ·
                    refine ⟨941584538248814503816841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2510892101996838676844909 941584538248814503816841)
                    ·
                      refine ⟨706188403686610877862631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941584538248814503816841 706188403686610877862631)
                      ·
                        rfl

theorem cell23_1375297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_1375297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375297 prefixEnd_1375297 := by exact prefixLift 1375297
  have htrace : WordTrace (prefixWord ++ tailWord_1375297) baseStart_1375297 baseEnd_1375297 := by
    simpa [prefixWord, tailWord_1375297, baseEnd_1375297] using wordTrace_append hprefix tailTrace_1375297
  have hstable : (prefixWord ++ tailWord_1375297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375297).length < 2 ^ (prefixWord ++ tailWord_1375297).sum := by decide
  have hdescent : baseEnd_1375297 < baseStart_1375297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375299 : List Nat := [1, 1, 1, 3, 1, 2, 6, 3, 5]
def baseStart_1375299 : Nat := 118140960795 + 1375299 * 2 ^ 59
def prefixEnd_1375299 : Nat := 4983230072969 + 3 ^ 40 * 1375299 * 2
def baseEnd_1375299 : Nat := 78465492294213318893069

theorem tailTrace_1375299 : CollatzResearch.WordTrace tailWord_1375299 prefixEnd_1375299 78465492294213318893069 := by
  unfold tailWord_1375299
  simp only [CollatzResearch.WordTrace]
  refine ⟨50161275444534080214368951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33440850296356053476245967 50161275444534080214368951)
  ·
    refine ⟨75241913166801120321553427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50161275444534080214368951 75241913166801120321553427)
    ·
      refine ⟨112862869750201680482330141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75241913166801120321553427 112862869750201680482330141)
      ·
        refine ⟨42323576156325630180873803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112862869750201680482330141 42323576156325630180873803)
        ·
          refine ⟨63485364234488445271310705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42323576156325630180873803 63485364234488445271310705)
          ·
            refine ⟨47614023175866333953483029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63485364234488445271310705 47614023175866333953483029)
            ·
              refine ⟨2231907336368734404069517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47614023175866333953483029 2231907336368734404069517)
              ·
                refine ⟨836965251138275401526069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2231907336368734404069517 836965251138275401526069)
                ·
                  refine ⟨78465492294213318893069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 836965251138275401526069 78465492294213318893069)
                  ·
                    rfl

theorem cell23_1375299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 5].length) (baseStart_1375299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375299 prefixEnd_1375299 := by exact prefixLift 1375299
  have htrace : WordTrace (prefixWord ++ tailWord_1375299) baseStart_1375299 baseEnd_1375299 := by
    simpa [prefixWord, tailWord_1375299, baseEnd_1375299] using wordTrace_append hprefix tailTrace_1375299
  have hstable : (prefixWord ++ tailWord_1375299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375299).length < 2 ^ (prefixWord ++ tailWord_1375299).sum := by decide
  have hdescent : baseEnd_1375299 < baseStart_1375299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375312 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 2, 5]
def baseStart_1375312 : Nat := 118140960795 + 1375312 * 2 ^ 59
def prefixEnd_1375312 : Nat := 4983230072969 + 3 ^ 40 * 1375312 * 2
def baseEnd_1375312 : Nat := 235398701965476106391687

theorem tailTrace_1375312 : CollatzResearch.WordTrace tailWord_1375312 prefixEnd_1375312 235398701965476106391687 := by
  unfold tailWord_1375312
  simp only [CollatzResearch.WordTrace]
  refine ⟨25080874796743491717296095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33441166395657988956394793 25080874796743491717296095)
  ·
    refine ⟨37621312195115237575944143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25080874796743491717296095 37621312195115237575944143)
    ·
      refine ⟨56431968292672856363916215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37621312195115237575944143 56431968292672856363916215)
      ·
        refine ⟨84647952439009284545874323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56431968292672856363916215 84647952439009284545874323)
        ·
          refine ⟨126971928658513926818811485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84647952439009284545874323 126971928658513926818811485)
          ·
            refine ⟨47614473246942722557054307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126971928658513926818811485 47614473246942722557054307)
            ·
              refine ⟨71421709870414083835581461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47614473246942722557054307 71421709870414083835581461)
              ·
                refine ⟨3347892650175660179792881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71421709870414083835581461 3347892650175660179792881)
                ·
                  refine ⟨2510919487631745134844661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3347892650175660179792881 2510919487631745134844661)
                  ·
                    refine ⟨235398701965476106391687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2510919487631745134844661 235398701965476106391687)
                    ·
                      rfl

theorem cell23_1375312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_1375312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375312 prefixEnd_1375312 := by exact prefixLift 1375312
  have htrace : WordTrace (prefixWord ++ tailWord_1375312) baseStart_1375312 baseEnd_1375312 := by
    simpa [prefixWord, tailWord_1375312, baseEnd_1375312] using wordTrace_append hprefix tailTrace_1375312
  have hstable : (prefixWord ++ tailWord_1375312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375312).length < 2 ^ (prefixWord ++ tailWord_1375312).sum := by decide
  have hdescent : baseEnd_1375312 < baseStart_1375312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375369 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 3]
def baseStart_1375369 : Nat := 118140960795 + 1375369 * 2 ^ 59
def prefixEnd_1375369 : Nat := 4983230072969 + 3 ^ 40 * 1375369 * 2
def baseEnd_1375369 : Nat := 706225374293734596162299

theorem tailTrace_1375369 : CollatzResearch.WordTrace tailWord_1375369 prefixEnd_1375369 706225374293734596162299 := by
  unfold tailWord_1375369
  simp only [CollatzResearch.WordTrace]
  refine ⟨50163828554280482169417161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33442552369520321446278107 50163828554280482169417161)
  ·
    refine ⟨37622871415710361627062871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50163828554280482169417161 37622871415710361627062871)
    ·
      refine ⟨56434307123565542440594307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37622871415710361627062871 56434307123565542440594307)
      ·
        refine ⟨84651460685348313660891461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56434307123565542440594307 84651460685348313660891461)
        ·
          refine ⟨15872148878502808811417149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84651460685348313660891461 15872148878502808811417149)
          ·
            refine ⟨5952055829438553304281431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15872148878502808811417149 5952055829438553304281431)
            ·
              refine ⟨8928083744157829956422147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5952055829438553304281431 8928083744157829956422147)
              ·
                refine ⟨13392125616236744934633221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8928083744157829956422147 13392125616236744934633221)
                ·
                  refine ⟨2511023553044389675243729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13392125616236744934633221 2511023553044389675243729)
                  ·
                    refine ⟨1883267664783292256432797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2511023553044389675243729 1883267664783292256432797)
                    ·
                      refine ⟨706225374293734596162299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1883267664783292256432797 706225374293734596162299)
                      ·
                        rfl

theorem cell23_1375369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_1375369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375369 prefixEnd_1375369 := by exact prefixLift 1375369
  have htrace : WordTrace (prefixWord ++ tailWord_1375369) baseStart_1375369 baseEnd_1375369 := by
    simpa [prefixWord, tailWord_1375369, baseEnd_1375369] using wordTrace_append hprefix tailTrace_1375369
  have hstable : (prefixWord ++ tailWord_1375369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375369).length < 2 ^ (prefixWord ++ tailWord_1375369).sum := by decide
  have hdescent : baseEnd_1375369 < baseStart_1375369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375389 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 6]
def baseStart_1375389 : Nat := 118140960795 + 1375389 * 2 ^ 59
def prefixEnd_1375389 : Nat := 4983230072969 + 3 ^ 40 * 1375389 * 2
def baseEnd_1375389 : Nat := 78470627100758279768023

theorem tailTrace_1375389 : CollatzResearch.WordTrace tailWord_1375389 prefixEnd_1375389 78470627100758279768023 := by
  unfold tailWord_1375389
  simp only [CollatzResearch.WordTrace]
  refine ⟨50164558014208025585145221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33443038676138683723430147 50164558014208025585145221)
  ·
    refine ⟨9405854627664004797214729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50164558014208025585145221 9405854627664004797214729)
    ·
      refine ⟨7054390970748003597911047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9405854627664004797214729 7054390970748003597911047)
      ·
        refine ⟨10581586456122005396866571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7054390970748003597911047 10581586456122005396866571)
        ·
          refine ⟨15872379684183008095299857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10581586456122005396866571 15872379684183008095299857)
          ·
            refine ⟨11904284763137256071474893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15872379684183008095299857 11904284763137256071474893)
            ·
              refine ⟨4464106786176471026803085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11904284763137256071474893 4464106786176471026803085)
              ·
                refine ⟨1674040044816176635051157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4464106786176471026803085 1674040044816176635051157)
                ·
                  refine ⟨78470627100758279768023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1674040044816176635051157 78470627100758279768023)
                  ·
                    rfl

theorem cell23_1375389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_1375389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375389 prefixEnd_1375389 := by exact prefixLift 1375389
  have htrace : WordTrace (prefixWord ++ tailWord_1375389) baseStart_1375389 baseEnd_1375389 := by
    simpa [prefixWord, tailWord_1375389, baseEnd_1375389] using wordTrace_append hprefix tailTrace_1375389
  have hstable : (prefixWord ++ tailWord_1375389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375389).length < 2 ^ (prefixWord ++ tailWord_1375389).sum := by decide
  have hdescent : baseEnd_1375389 < baseStart_1375389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375449 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 6, 4]
def baseStart_1375449 : Nat := 118140960795 + 1375449 * 2 ^ 59
def prefixEnd_1375449 : Nat := 4983230072969 + 3 ^ 40 * 1375449 * 2
def baseEnd_1375449 : Nat := 235422150915364761053977

theorem tailTrace_1375449 : CollatzResearch.WordTrace tailWord_1375449 prefixEnd_1375449 235422150915364761053977 := by
  unfold tailWord_1375449
  simp only [CollatzResearch.WordTrace]
  refine ⟨50166746393990655832329401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33444497595993770554886267 50166746393990655832329401)
  ·
    refine ⟨37625059795492991874247051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50166746393990655832329401 37625059795492991874247051)
    ·
      refine ⟨56437589693239487811370577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37625059795492991874247051 56437589693239487811370577)
      ·
        refine ⟨42328192269929615858527933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56437589693239487811370577 42328192269929615858527933)
        ·
          refine ⟨15873072101223605946947975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42328192269929615858527933 15873072101223605946947975)
          ·
            refine ⟨23809608151835408920421963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15873072101223605946947975 23809608151835408920421963)
            ·
              refine ⟨35714412227753113380632945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23809608151835408920421963 35714412227753113380632945)
              ·
                refine ⟨26785809170814835035474709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35714412227753113380632945 26785809170814835035474709)
                ·
                  refine ⟨1255584804881945392287877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26785809170814835035474709 1255584804881945392287877)
                  ·
                    refine ⟨235422150915364761053977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1255584804881945392287877 235422150915364761053977)
                    ·
                      rfl

theorem cell23_1375449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 4].length) (baseStart_1375449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375449 prefixEnd_1375449 := by exact prefixLift 1375449
  have htrace : WordTrace (prefixWord ++ tailWord_1375449) baseStart_1375449 baseEnd_1375449 := by
    simpa [prefixWord, tailWord_1375449, baseEnd_1375449] using wordTrace_append hprefix tailTrace_1375449
  have hstable : (prefixWord ++ tailWord_1375449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375449).length < 2 ^ (prefixWord ++ tailWord_1375449).sum := by decide
  have hdescent : baseEnd_1375449 < baseStart_1375449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375540 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1375540 : Nat := 118140960795 + 1375540 * 2 ^ 59
def prefixEnd_1375540 : Nat := 4983230072969 + 3 ^ 40 * 1375540 * 2
def baseEnd_1375540 : Nat := 706313179485653427124013

theorem tailTrace_1375540 : CollatzResearch.WordTrace tailWord_1375540 prefixEnd_1375540 706313179485653427124013 := by
  unfold tailWord_1375540
  simp only [CollatzResearch.WordTrace]
  refine ⟨25085032718330489186946037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33446710291107318915928049 25085032718330489186946037)
  ·
    refine ⟨2351721817343483361276191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25085032718330489186946037 2351721817343483361276191)
    ·
      refine ⟨3527582726015225041914287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2351721817343483361276191 3527582726015225041914287)
      ·
        refine ⟨5291374089022837562871431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527582726015225041914287 5291374089022837562871431)
        ·
          refine ⟨7937061133534256344307147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5291374089022837562871431 7937061133534256344307147)
          ·
            refine ⟨11905591700301384516460721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7937061133534256344307147 11905591700301384516460721)
            ·
              refine ⟨8929193775226038387345541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11905591700301384516460721 8929193775226038387345541)
              ·
                refine ⟨1674223832854882197627289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8929193775226038387345541 1674223832854882197627289)
                ·
                  refine ⟨1255667874641161648220467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674223832854882197627289 1255667874641161648220467)
                  ·
                    refine ⟨1883501811961742472330701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1255667874641161648220467 1883501811961742472330701)
                    ·
                      refine ⟨706313179485653427124013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1883501811961742472330701 706313179485653427124013)
                      ·
                        rfl

theorem cell23_1375540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1375540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375540 prefixEnd_1375540 := by exact prefixLift 1375540
  have htrace : WordTrace (prefixWord ++ tailWord_1375540) baseStart_1375540 baseEnd_1375540 := by
    simpa [prefixWord, tailWord_1375540, baseEnd_1375540] using wordTrace_append hprefix tailTrace_1375540
  have hstable : (prefixWord ++ tailWord_1375540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375540).length < 2 ^ (prefixWord ++ tailWord_1375540).sum := by decide
  have hdescent : baseEnd_1375540 < baseStart_1375540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375569 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 9]
def baseStart_1375569 : Nat := 118140960795 + 1375569 * 2 ^ 59
def prefixEnd_1375569 : Nat := 4983230072969 + 3 ^ 40 * 1375569 * 2
def baseEnd_1375569 : Nat := 78480896713848201517931

theorem tailTrace_1375569 : CollatzResearch.WordTrace tailWord_1375569 prefixEnd_1375569 78480896713848201517931 := by
  unfold tailWord_1375569
  simp only [CollatzResearch.WordTrace]
  refine ⟨50171123153555916326697761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33447415435703944217798507 50171123153555916326697761)
  ·
    refine ⟨37628342365166937245023321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50171123153555916326697761 37628342365166937245023321)
    ·
      refine ⟨28221256773875202933767491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37628342365166937245023321 28221256773875202933767491)
      ·
        refine ⟨42331885160812804400651237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28221256773875202933767491 42331885160812804400651237)
        ·
          refine ⟨7937228467652400825122107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42331885160812804400651237 7937228467652400825122107)
          ·
            refine ⟨11905842701478601237683161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7937228467652400825122107 11905842701478601237683161)
            ·
              refine ⟨8929382026108950928262371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11905842701478601237683161 8929382026108950928262371)
              ·
                refine ⟨13394073039163426392393557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8929382026108950928262371 13394073039163426392393557)
                ·
                  refine ⟨78480896713848201517931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13394073039163426392393557 78480896713848201517931)
                  ·
                    rfl

theorem cell23_1375569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 9].length) (baseStart_1375569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375569 prefixEnd_1375569 := by exact prefixLift 1375569
  have htrace : WordTrace (prefixWord ++ tailWord_1375569) baseStart_1375569 baseEnd_1375569 := by
    simpa [prefixWord, tailWord_1375569, baseEnd_1375569] using wordTrace_append hprefix tailTrace_1375569
  have hstable : (prefixWord ++ tailWord_1375569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375569).length < 2 ^ (prefixWord ++ tailWord_1375569).sum := by decide
  have hdescent : baseEnd_1375569 < baseStart_1375569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375574 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1375574 : Nat := 118140960795 + 1375574 * 2 ^ 59
def prefixEnd_1375574 : Nat := 4983230072969 + 3 ^ 40 * 1375574 * 2
def baseEnd_1375574 : Nat := 706330637827906294098857

theorem tailTrace_1375574 : CollatzResearch.WordTrace tailWord_1375574 prefixEnd_1375574 706330637827906294098857 := by
  unfold tailWord_1375574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135706594908612636289361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33447537012358534787086517 3135706594908612636289361)
  ·
    refine ⟨2351779946181459477217021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3135706594908612636289361 2351779946181459477217021)
    ·
      refine ⟨881917479818047303956383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2351779946181459477217021 881917479818047303956383)
      ·
        refine ⟨1322876219727070955934575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881917479818047303956383 1322876219727070955934575)
        ·
          refine ⟨1984314329590606433901863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322876219727070955934575 1984314329590606433901863)
          ·
            refine ⟨2976471494385909650852795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984314329590606433901863 2976471494385909650852795)
            ·
              refine ⟨4464707241578864476279193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976471494385909650852795 4464707241578864476279193)
              ·
                refine ⟨3348530431184148357209395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4464707241578864476279193 3348530431184148357209395)
                ·
                  refine ⟨5022795646776222535814093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348530431184148357209395 5022795646776222535814093)
                  ·
                    refine ⟨1883548367541083450930285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5022795646776222535814093 1883548367541083450930285)
                    ·
                      refine ⟨706330637827906294098857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1883548367541083450930285 706330637827906294098857)
                      ·
                        rfl

theorem cell23_1375574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1375574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375574 prefixEnd_1375574 := by exact prefixLift 1375574
  have htrace : WordTrace (prefixWord ++ tailWord_1375574) baseStart_1375574 baseEnd_1375574 := by
    simpa [prefixWord, tailWord_1375574, baseEnd_1375574] using wordTrace_append hprefix tailTrace_1375574
  have hstable : (prefixWord ++ tailWord_1375574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375574).length < 2 ^ (prefixWord ++ tailWord_1375574).sum := by decide
  have hdescent : baseEnd_1375574 < baseStart_1375574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375597 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_1375597 : Nat := 118140960795 + 1375597 * 2 ^ 59
def prefixEnd_1375597 : Nat := 4983230072969 + 3 ^ 40 * 1375597 * 2
def baseEnd_1375597 : Nat := 706342447882959704111251

theorem tailTrace_1375597 : CollatzResearch.WordTrace tailWord_1375597 prefixEnd_1375597 706342447882959704111251 := by
  unfold tailWord_1375597
  simp only [CollatzResearch.WordTrace]
  refine ⟨50172144397454477108717045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33448096264969651405811363 50172144397454477108717045)
  ·
    refine ⟨4703638537261357228942223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50172144397454477108717045 4703638537261357228942223)
    ·
      refine ⟨7055457805892035843413335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4703638537261357228942223 7055457805892035843413335)
      ·
        refine ⟨10583186708838053765120003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7055457805892035843413335 10583186708838053765120003)
        ·
          refine ⟨15874780063257080647680005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10583186708838053765120003 15874780063257080647680005)
          ·
            refine ⟨2976521261860702621440001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15874780063257080647680005 2976521261860702621440001)
            ·
              refine ⟨2232390946395526966080001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2976521261860702621440001 2232390946395526966080001)
              ·
                refine ⟨1674293209796645224560001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232390946395526966080001 1674293209796645224560001)
                ·
                  refine ⟨1255719907347483918420001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674293209796645224560001 1255719907347483918420001)
                  ·
                    refine ⟨941789930510612938815001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1255719907347483918420001 941789930510612938815001)
                    ·
                      refine ⟨706342447882959704111251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941789930510612938815001 706342447882959704111251)
                      ·
                        rfl

theorem cell23_1375597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_1375597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375597 prefixEnd_1375597 := by exact prefixLift 1375597
  have htrace : WordTrace (prefixWord ++ tailWord_1375597) baseStart_1375597 baseEnd_1375597 := by
    simpa [prefixWord, tailWord_1375597, baseEnd_1375597] using wordTrace_append hprefix tailTrace_1375597
  have hstable : (prefixWord ++ tailWord_1375597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375597).length < 2 ^ (prefixWord ++ tailWord_1375597).sum := by decide
  have hdescent : baseEnd_1375597 < baseStart_1375597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375614 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1375614 : Nat := 118140960795 + 1375614 * 2 ^ 59
def prefixEnd_1375614 : Nat := 4983230072969 + 3 ^ 40 * 1375614 * 2
def baseEnd_1375614 : Nat := 706351177054086137598673

theorem tailTrace_1375614 : CollatzResearch.WordTrace tailWord_1375614 prefixEnd_1375614 706351177054086137598673 := by
  unfold tailWord_1375614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6271595554799111126510737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33448509625595259341390597 6271595554799111126510737)
  ·
    refine ⟨4703696666099333344883053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6271595554799111126510737 4703696666099333344883053)
    ·
      refine ⟨1763886249787250004331145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4703696666099333344883053 1763886249787250004331145)
      ·
        refine ⟨1322914687340437503248359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1763886249787250004331145 1322914687340437503248359)
        ·
          refine ⟨1984372031010656254872539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322914687340437503248359 1984372031010656254872539)
          ·
            refine ⟨2976558046515984382308809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984372031010656254872539 2976558046515984382308809)
            ·
              refine ⟨2232418534886988286731607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2976558046515984382308809 2232418534886988286731607)
              ·
                refine ⟨3348627802330482430097411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232418534886988286731607 3348627802330482430097411)
                ·
                  refine ⟨5022941703495723645146117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348627802330482430097411 5022941703495723645146117)
                  ·
                    refine ⟨941801569405448183464897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5022941703495723645146117 941801569405448183464897)
                    ·
                      refine ⟨706351177054086137598673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 941801569405448183464897 706351177054086137598673)
                      ·
                        rfl

theorem cell23_1375614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1375614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375614 prefixEnd_1375614 := by exact prefixLift 1375614
  have htrace : WordTrace (prefixWord ++ tailWord_1375614) baseStart_1375614 baseEnd_1375614 := by
    simpa [prefixWord, tailWord_1375614, baseEnd_1375614] using wordTrace_append hprefix tailTrace_1375614
  have hstable : (prefixWord ++ tailWord_1375614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375614).length < 2 ^ (prefixWord ++ tailWord_1375614).sum := by decide
  have hdescent : baseEnd_1375614 < baseStart_1375614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375703 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_1375703 : Nat := 118140960795 + 1375703 * 2 ^ 59
def prefixEnd_1375703 : Nat := 4983230072969 + 3 ^ 40 * 1375703 * 2
def baseEnd_1375703 : Nat := 706396876832336289385763

theorem tailTrace_1375703 : CollatzResearch.WordTrace tailWord_1375703 prefixEnd_1375703 706396876832336289385763 := by
  unfold tailWord_1375703
  simp only [CollatzResearch.WordTrace]
  refine ⟨50176010535070457212075763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33450673690046971474717175 50176010535070457212075763)
  ·
    refine ⟨75264015802605685818113645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50176010535070457212075763 75264015802605685818113645)
    ·
      refine ⟨28224005925977132181792617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75264015802605685818113645 28224005925977132181792617)
      ·
        refine ⟨21168004444482849136344463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28224005925977132181792617 21168004444482849136344463)
        ·
          refine ⟨31752006666724273704516695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21168004444482849136344463 31752006666724273704516695)
          ·
            refine ⟨47628010000086410556775043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31752006666724273704516695 47628010000086410556775043)
            ·
              refine ⟨71442015000129615835162565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47628010000086410556775043 71442015000129615835162565)
              ·
                refine ⟨13395377812524302969092981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71442015000129615835162565 13395377812524302969092981)
                ·
                  refine ⟨1255816669924153403352467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13395377812524302969092981 1255816669924153403352467)
                  ·
                    refine ⟨1883725004886230105028701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1255816669924153403352467 1883725004886230105028701)
                    ·
                      refine ⟨706396876832336289385763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1883725004886230105028701 706396876832336289385763)
                      ·
                        rfl

theorem cell23_1375703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_1375703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375703 prefixEnd_1375703 := by exact prefixLift 1375703
  have htrace : WordTrace (prefixWord ++ tailWord_1375703) baseStart_1375703 baseEnd_1375703 := by
    simpa [prefixWord, tailWord_1375703, baseEnd_1375703] using wordTrace_append hprefix tailTrace_1375703
  have hstable : (prefixWord ++ tailWord_1375703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375703).length < 2 ^ (prefixWord ++ tailWord_1375703).sum := by decide
  have hdescent : baseEnd_1375703 < baseStart_1375703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375743 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 4]
def baseStart_1375743 : Nat := 118140960795 + 1375743 * 2 ^ 59
def prefixEnd_1375743 : Nat := 4983230072969 + 3 ^ 40 * 1375743 * 2
def baseEnd_1375743 : Nat := 706417416058516132885579

theorem tailTrace_1375743 : CollatzResearch.WordTrace tailWord_1375743 prefixEnd_1375743 706417416058516132885579 := by
  unfold tailWord_1375743
  simp only [CollatzResearch.WordTrace]
  refine ⟨50177469454925544043531883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33451646303283696029021255 50177469454925544043531883)
  ·
    refine ⟨75266204182388316065297825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50177469454925544043531883 75266204182388316065297825)
    ·
      refine ⟨56449653136791237048973369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75266204182388316065297825 56449653136791237048973369)
      ·
        refine ⟨42337239852593427786730027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56449653136791237048973369 42337239852593427786730027)
        ·
          refine ⟨63505859778890141680095041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42337239852593427786730027 63505859778890141680095041)
          ·
            refine ⟨47629394834167606260071281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63505859778890141680095041 47629394834167606260071281)
            ·
              refine ⟨35722046125625704695053461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47629394834167606260071281 35722046125625704695053461)
              ·
                refine ⟨1674470912138704907580631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35722046125625704695053461 1674470912138704907580631)
                ·
                  refine ⟨2511706368208057361370947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674470912138704907580631 2511706368208057361370947)
                  ·
                    refine ⟨3767559552312086042056421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2511706368208057361370947 3767559552312086042056421)
                    ·
                      refine ⟨706417416058516132885579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3767559552312086042056421 706417416058516132885579)
                      ·
                        rfl

theorem cell23_1375743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_1375743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375743 prefixEnd_1375743 := by exact prefixLift 1375743
  have htrace : WordTrace (prefixWord ++ tailWord_1375743) baseStart_1375743 baseEnd_1375743 := by
    simpa [prefixWord, tailWord_1375743, baseEnd_1375743] using wordTrace_append hprefix tailTrace_1375743
  have hstable : (prefixWord ++ tailWord_1375743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375743).length < 2 ^ (prefixWord ++ tailWord_1375743).sum := by decide
  have hdescent : baseEnd_1375743 < baseStart_1375743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375763 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 5]
def baseStart_1375763 : Nat := 118140960795 + 1375763 * 2 ^ 59
def prefixEnd_1375763 : Nat := 4983230072969 + 3 ^ 40 * 1375763 * 2
def baseEnd_1375763 : Nat := 706427685671606054635487

theorem tailTrace_1375763 : CollatzResearch.WordTrace tailWord_1375763 prefixEnd_1375763 706427685671606054635487 := by
  unfold tailWord_1375763
  simp only [CollatzResearch.WordTrace]
  refine ⟨50178198914853087459259943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33452132609902058306173295 50178198914853087459259943)
  ·
    refine ⟨75267298372279631188889915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50178198914853087459259943 75267298372279631188889915)
    ·
      refine ⟨112900947558419446783334873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75267298372279631188889915 112900947558419446783334873)
      ·
        refine ⟨84675710668814585087501155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112900947558419446783334873 84675710668814585087501155)
        ·
          refine ⟨127013566003221877631251733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84675710668814585087501155 127013566003221877631251733)
          ·
            refine ⟨5953760906401025513964925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127013566003221877631251733 5953760906401025513964925)
            ·
              refine ⟨2232660339900384567736847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5953760906401025513964925 2232660339900384567736847)
              ·
                refine ⟨3348990509850576851605271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232660339900384567736847 3348990509850576851605271)
                ·
                  refine ⟨5023485764775865277407907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348990509850576851605271 5023485764775865277407907)
                  ·
                    refine ⟨7535228647163797916111861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5023485764775865277407907 7535228647163797916111861)
                    ·
                      refine ⟨706427685671606054635487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7535228647163797916111861 706427685671606054635487)
                      ·
                        rfl

theorem cell23_1375763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_1375763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375763 prefixEnd_1375763 := by exact prefixLift 1375763
  have htrace : WordTrace (prefixWord ++ tailWord_1375763) baseStart_1375763 baseEnd_1375763 := by
    simpa [prefixWord, tailWord_1375763, baseEnd_1375763] using wordTrace_append hprefix tailTrace_1375763
  have hstable : (prefixWord ++ tailWord_1375763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375763).length < 2 ^ (prefixWord ++ tailWord_1375763).sum := by decide
  have hdescent : baseEnd_1375763 < baseStart_1375763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375773 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1375773 : Nat := 118140960795 + 1375773 * 2 ^ 59
def prefixEnd_1375773 : Nat := 4983230072969 + 3 ^ 40 * 1375773 * 2
def baseEnd_1375773 : Nat := 706432820478151015510441

theorem tailTrace_1375773 : CollatzResearch.WordTrace tailWord_1375773 prefixEnd_1375773 706432820478151015510441 := by
  unfold tailWord_1375773
  simp only [CollatzResearch.WordTrace]
  refine ⟨50178563644816859167123973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33452375763211239444749315 50178563644816859167123973)
  ·
    refine ⟨9408480683403161093835745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50178563644816859167123973 9408480683403161093835745)
    ·
      refine ⟨7056360512552370820376809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9408480683403161093835745 7056360512552370820376809)
      ·
        refine ⟨5292270384414278115282607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7056360512552370820376809 5292270384414278115282607)
        ·
          refine ⟨7938405576621417172923911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292270384414278115282607 7938405576621417172923911)
          ·
            refine ⟨11907608364932125759385867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7938405576621417172923911 11907608364932125759385867)
            ·
              refine ⟨17861412547398188639078801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11907608364932125759385867 17861412547398188639078801)
              ·
                refine ⟨13396059410548641479309101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17861412547398188639078801 13396059410548641479309101)
                ·
                  refine ⟨5023522278955740554740913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13396059410548641479309101 5023522278955740554740913)
                  ·
                    refine ⟨3767641709216805416055685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5023522278955740554740913 3767641709216805416055685)
                    ·
                      refine ⟨706432820478151015510441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3767641709216805416055685 706432820478151015510441)
                      ·
                        rfl

theorem cell23_1375773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1375773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375773 prefixEnd_1375773 := by exact prefixLift 1375773
  have htrace : WordTrace (prefixWord ++ tailWord_1375773) baseStart_1375773 baseEnd_1375773 := by
    simpa [prefixWord, tailWord_1375773, baseEnd_1375773] using wordTrace_append hprefix tailTrace_1375773
  have hstable : (prefixWord ++ tailWord_1375773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375773).length < 2 ^ (prefixWord ++ tailWord_1375773).sum := by decide
  have hdescent : baseEnd_1375773 < baseStart_1375773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375790 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1375790 : Nat := 118140960795 + 1375790 * 2 ^ 59
def prefixEnd_1375790 : Nat := 4983230072969 + 3 ^ 40 * 1375790 * 2
def baseEnd_1375790 : Nat := 706441549649277448997863

theorem tailTrace_1375790 : CollatzResearch.WordTrace tailWord_1375790 prefixEnd_1375790 706441549649277448997863 := by
  unfold tailWord_1375790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6272397960719408883811603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33452789123836847380328549 6272397960719408883811603)
  ·
    refine ⟨9408596941079113325717405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6272397960719408883811603 9408596941079113325717405)
    ·
      refine ⟨3528223852904667497144027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9408596941079113325717405 3528223852904667497144027)
      ·
        refine ⟨5292335779357001245716041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528223852904667497144027 5292335779357001245716041)
        ·
          refine ⟨3969251834517750934287031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5292335779357001245716041 3969251834517750934287031)
          ·
            refine ⟨5953877751776626401430547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969251834517750934287031 5953877751776626401430547)
            ·
              refine ⟨8930816627664939602145821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953877751776626401430547 8930816627664939602145821)
              ·
                refine ⟨3349056235374352350804683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8930816627664939602145821 3349056235374352350804683)
                ·
                  refine ⟨5023584353061528526207025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349056235374352350804683 5023584353061528526207025)
                  ·
                    refine ⟨3767688264796146394655269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5023584353061528526207025 3767688264796146394655269)
                    ·
                      refine ⟨706441549649277448997863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3767688264796146394655269 706441549649277448997863)
                      ·
                        rfl

theorem cell23_1375790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1375790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375790 prefixEnd_1375790 := by exact prefixLift 1375790
  have htrace : WordTrace (prefixWord ++ tailWord_1375790) baseStart_1375790 baseEnd_1375790 := by
    simpa [prefixWord, tailWord_1375790, baseEnd_1375790] using wordTrace_append hprefix tailTrace_1375790
  have hstable : (prefixWord ++ tailWord_1375790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375790).length < 2 ^ (prefixWord ++ tailWord_1375790).sum := by decide
  have hdescent : baseEnd_1375790 < baseStart_1375790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375821 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1375821 : Nat := 118140960795 + 1375821 * 2 ^ 59
def prefixEnd_1375821 : Nat := 4983230072969 + 3 ^ 40 * 1375821 * 2
def baseEnd_1375821 : Nat := 235485822516522275903407

theorem tailTrace_1375821 : CollatzResearch.WordTrace tailWord_1375821 prefixEnd_1375821 235485822516522275903407 := by
  unfold tailWord_1375821
  simp only [CollatzResearch.WordTrace]
  refine ⟨50180314348642963364871317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33453542899095308909914211 50180314348642963364871317)
  ·
    refine ⟨2352202235092638907728343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50180314348642963364871317 2352202235092638907728343)
    ·
      refine ⟨3528303352638958361592515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2352202235092638907728343 3528303352638958361592515)
      ·
        refine ⟨5292455028958437542388773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528303352638958361592515 5292455028958437542388773)
        ·
          refine ⟨992335317929707039197895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5292455028958437542388773 992335317929707039197895)
          ·
            refine ⟨1488502976894560558796843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992335317929707039197895 1488502976894560558796843)
            ·
              refine ⟨2232754465341840838195265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488502976894560558796843 2232754465341840838195265)
              ·
                refine ⟨1674565849006380628646449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232754465341840838195265 1674565849006380628646449)
                ·
                  refine ⟨1255924386754785471484837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674565849006380628646449 1255924386754785471484837)
                  ·
                    refine ⟨235485822516522275903407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1255924386754785471484837 235485822516522275903407)
                    ·
                      rfl

theorem cell23_1375821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1375821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375821 prefixEnd_1375821 := by exact prefixLift 1375821
  have htrace : WordTrace (prefixWord ++ tailWord_1375821) baseStart_1375821 baseEnd_1375821 := by
    simpa [prefixWord, tailWord_1375821, baseEnd_1375821] using wordTrace_append hprefix tailTrace_1375821
  have hstable : (prefixWord ++ tailWord_1375821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375821).length < 2 ^ (prefixWord ++ tailWord_1375821).sum := by decide
  have hdescent : baseEnd_1375821 < baseStart_1375821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375843 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 2, 6]
def baseStart_1375843 : Nat := 118140960795 + 1375843 * 2 ^ 59
def prefixEnd_1375843 : Nat := 4983230072969 + 3 ^ 40 * 1375843 * 2
def baseEnd_1375843 : Nat := 235489588041321913878373

theorem tailTrace_1375843 : CollatzResearch.WordTrace tailWord_1375843 prefixEnd_1375843 235489588041321913878373 := by
  unfold tailWord_1375843
  simp only [CollatzResearch.WordTrace]
  refine ⟨50181116754563261122172183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33454077836375507414781455 50181116754563261122172183)
  ·
    refine ⟨75271675131844891683258275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50181116754563261122172183 75271675131844891683258275)
    ·
      refine ⟨112907512697767337524887413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75271675131844891683258275 112907512697767337524887413)
      ·
        refine ⟨10585079315415687892958195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112907512697767337524887413 10585079315415687892958195)
        ·
          refine ⟨15877618973123531839437293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10585079315415687892958195 15877618973123531839437293)
          ·
            refine ⟨5954107114921324439788985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15877618973123531839437293 5954107114921324439788985)
            ·
              refine ⟨4465580336190993329841739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5954107114921324439788985 4465580336190993329841739)
              ·
                refine ⟨6698370504286489994762609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465580336190993329841739 6698370504286489994762609)
                ·
                  refine ⟨5023777878214867496071957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6698370504286489994762609 5023777878214867496071957)
                  ·
                    refine ⟨235489588041321913878373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5023777878214867496071957 235489588041321913878373)
                    ·
                      rfl

theorem cell23_1375843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 6].length) (baseStart_1375843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375843 prefixEnd_1375843 := by exact prefixLift 1375843
  have htrace : WordTrace (prefixWord ++ tailWord_1375843) baseStart_1375843 baseEnd_1375843 := by
    simpa [prefixWord, tailWord_1375843, baseEnd_1375843] using wordTrace_append hprefix tailTrace_1375843
  have hstable : (prefixWord ++ tailWord_1375843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375843).length < 2 ^ (prefixWord ++ tailWord_1375843).sum := by decide
  have hdescent : baseEnd_1375843 < baseStart_1375843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375844 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_1375844 : Nat := 118140960795 + 1375844 * 2 ^ 59
def prefixEnd_1375844 : Nat := 4983230072969 + 3 ^ 40 * 1375844 * 2
def baseEnd_1375844 : Nat := 706469277604620237722615

theorem tailTrace_1375844 : CollatzResearch.WordTrace tailWord_1375844 prefixEnd_1375844 706469277604620237722615 := by
  unfold tailWord_1375844
  simp only [CollatzResearch.WordTrace]
  refine ⟨25090576613779819146479293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33454102151706425528639057 25090576613779819146479293)
  ·
    refine ⟨9408966230167432179929735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25090576613779819146479293 9408966230167432179929735)
    ·
      refine ⟨14113449345251148269894603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9408966230167432179929735 14113449345251148269894603)
      ·
        refine ⟨21170174017876722404841905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14113449345251148269894603 21170174017876722404841905)
        ·
          refine ⟨15877630513407541803631429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21170174017876722404841905 15877630513407541803631429)
          ·
            refine ⟨2977055721263914088180893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15877630513407541803631429 2977055721263914088180893)
            ·
              refine ⟨1116395895473967783067835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2977055721263914088180893 1116395895473967783067835)
              ·
                refine ⟨1674593843210951674601753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116395895473967783067835 1674593843210951674601753)
                ·
                  refine ⟨1255945382408213755951315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674593843210951674601753 1255945382408213755951315)
                  ·
                    refine ⟨1883918073612320633926973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1255945382408213755951315 1883918073612320633926973)
                    ·
                      refine ⟨706469277604620237722615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1883918073612320633926973 706469277604620237722615)
                      ·
                        rfl

theorem cell23_1375844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_1375844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375844 prefixEnd_1375844 := by exact prefixLift 1375844
  have htrace : WordTrace (prefixWord ++ tailWord_1375844) baseStart_1375844 baseEnd_1375844 := by
    simpa [prefixWord, tailWord_1375844, baseEnd_1375844] using wordTrace_append hprefix tailTrace_1375844
  have hstable : (prefixWord ++ tailWord_1375844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375844).length < 2 ^ (prefixWord ++ tailWord_1375844).sum := by decide
  have hdescent : baseEnd_1375844 < baseStart_1375844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375943 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1375943 : Nat := 118140960795 + 1375943 * 2 ^ 59
def prefixEnd_1375943 : Nat := 4983230072969 + 3 ^ 40 * 1375943 * 2
def baseEnd_1375943 : Nat := 706520112189415350384659

theorem tailTrace_1375943 : CollatzResearch.WordTrace tailWord_1375943 prefixEnd_1375943 706520112189415350384659 := by
  unfold tailWord_1375943
  simp only [CollatzResearch.WordTrace]
  refine ⟨50184764054200978200812483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33456509369467318800541655 50184764054200978200812483)
  ·
    refine ⟨75277146081301467301218725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50184764054200978200812483 75277146081301467301218725)
    ·
      refine ⟨14114464890244025118978511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75277146081301467301218725 14114464890244025118978511)
      ·
        refine ⟨21171697335366037678467767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14114464890244025118978511 21171697335366037678467767)
        ·
          refine ⟨31757546003049056517701651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21171697335366037678467767 31757546003049056517701651)
          ·
            refine ⟨47636319004573584776552477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31757546003049056517701651 47636319004573584776552477)
            ·
              refine ⟨17863619626715094291207179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47636319004573584776552477 17863619626715094291207179)
              ·
                refine ⟨26795429440072641436810769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17863619626715094291207179 26795429440072641436810769)
                ·
                  refine ⟨20096572080054481077608077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26795429440072641436810769 20096572080054481077608077)
                  ·
                    refine ⟨7536214530020430404103029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20096572080054481077608077 7536214530020430404103029)
                    ·
                      refine ⟨706520112189415350384659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7536214530020430404103029 706520112189415350384659)
                      ·
                        rfl

theorem cell23_1375943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1375943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375943 prefixEnd_1375943 := by exact prefixLift 1375943
  have htrace : WordTrace (prefixWord ++ tailWord_1375943) baseStart_1375943 baseEnd_1375943 := by
    simpa [prefixWord, tailWord_1375943, baseEnd_1375943] using wordTrace_append hprefix tailTrace_1375943
  have hstable : (prefixWord ++ tailWord_1375943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375943).length < 2 ^ (prefixWord ++ tailWord_1375943).sum := by decide
  have hdescent : baseEnd_1375943 < baseStart_1375943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375960 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1375960 : Nat := 118140960795 + 1375960 * 2 ^ 59
def prefixEnd_1375960 : Nat := 4983230072969 + 3 ^ 40 * 1375960 * 2
def baseEnd_1375960 : Nat := 706528841360541783872081

theorem tailTrace_1375960 : CollatzResearch.WordTrace tailWord_1375960 prefixEnd_1375960 706528841360541783872081 := by
  unfold tailWord_1375960
  simp only [CollatzResearch.WordTrace]
  refine ⟨25092692047569695052090667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33456922730092926736120889 25092692047569695052090667)
  ·
    refine ⟨37639038071354542578136001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25092692047569695052090667 37639038071354542578136001)
    ·
      refine ⟨28229278553515906933602001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37639038071354542578136001 28229278553515906933602001)
      ·
        refine ⟨21171958915136930200201501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28229278553515906933602001 21171958915136930200201501)
        ·
          refine ⟨7939484593176348825075563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21171958915136930200201501 7939484593176348825075563)
          ·
            refine ⟨11909226889764523237613345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939484593176348825075563 11909226889764523237613345)
            ·
              refine ⟨8931920167323392428210009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11909226889764523237613345 8931920167323392428210009)
              ·
                refine ⟨6698940125492544321157507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8931920167323392428210009 6698940125492544321157507)
                ·
                  refine ⟨10048410188238816481736261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698940125492544321157507 10048410188238816481736261)
                  ·
                    refine ⟨1884076910294778090325549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10048410188238816481736261 1884076910294778090325549)
                    ·
                      refine ⟨706528841360541783872081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1884076910294778090325549 706528841360541783872081)
                      ·
                        rfl

theorem cell23_1375960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1375960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1375960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1375960 prefixEnd_1375960 := by exact prefixLift 1375960
  have htrace : WordTrace (prefixWord ++ tailWord_1375960) baseStart_1375960 baseEnd_1375960 := by
    simpa [prefixWord, tailWord_1375960, baseEnd_1375960] using wordTrace_append hprefix tailTrace_1375960
  have hstable : (prefixWord ++ tailWord_1375960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375960).length < 2 ^ (prefixWord ++ tailWord_1375960).sum := by decide
  have hdescent : baseEnd_1375960 < baseStart_1375960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376034 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_1376034 : Nat := 118140960795 + 1376034 * 2 ^ 59
def prefixEnd_1376034 : Nat := 4983230072969 + 3 ^ 40 * 1376034 * 2
def baseEnd_1376034 : Nat := 706566838928974494346741

theorem tailTrace_1376034 : CollatzResearch.WordTrace tailWord_1376034 prefixEnd_1376034 706566838928974494346741 := by
  unfold tailWord_1376034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12547020774217825185593789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33458722064580867161583437 12547020774217825185593789)
  ·
    refine ⟨4705132790331684444597671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12547020774217825185593789 4705132790331684444597671)
    ·
      refine ⟨7057699185497526666896507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4705132790331684444597671 7057699185497526666896507)
      ·
        refine ⟨10586548778246290000344761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7057699185497526666896507 10586548778246290000344761)
        ·
          refine ⟨7939911583684717500258571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10586548778246290000344761 7939911583684717500258571)
          ·
            refine ⟨11909867375527076250387857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939911583684717500258571 11909867375527076250387857)
            ·
              refine ⟨8932400531645307187790893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11909867375527076250387857 8932400531645307187790893)
              ·
                refine ⟨3349650199366990195421585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8932400531645307187790893 3349650199366990195421585)
                ·
                  refine ⟨2512237649525242646566189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3349650199366990195421585 2512237649525242646566189)
                  ·
                    refine ⟨942089118571965992462321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512237649525242646566189 942089118571965992462321)
                    ·
                      refine ⟨706566838928974494346741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942089118571965992462321 706566838928974494346741)
                      ·
                        rfl

theorem cell23_1376034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_1376034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376034 prefixEnd_1376034 := by exact prefixLift 1376034
  have htrace : WordTrace (prefixWord ++ tailWord_1376034) baseStart_1376034 baseEnd_1376034 := by
    simpa [prefixWord, tailWord_1376034, baseEnd_1376034] using wordTrace_append hprefix tailTrace_1376034
  have hstable : (prefixWord ++ tailWord_1376034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376034).length < 2 ^ (prefixWord ++ tailWord_1376034).sum := by decide
  have hdescent : baseEnd_1376034 < baseStart_1376034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376058 : List Nat := [3, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3]
def baseStart_1376058 : Nat := 118140960795 + 1376058 * 2 ^ 59
def prefixEnd_1376058 : Nat := 4983230072969 + 3 ^ 40 * 1376058 * 2
def baseEnd_1376058 : Nat := 706579162464682400446631

theorem tailTrace_1376058 : CollatzResearch.WordTrace tailWord_1376058 prefixEnd_1376058 706579162464682400446631 := by
  unfold tailWord_1376058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12547239612196088210312207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33459305632522901894165885 12547239612196088210312207)
  ·
    refine ⟨18820859418294132315468311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12547239612196088210312207 18820859418294132315468311)
    ·
      refine ⟨28231289127441198473202467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18820859418294132315468311 28231289127441198473202467)
      ·
        refine ⟨42346933691161797709803701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28231289127441198473202467 42346933691161797709803701)
        ·
          refine ⟨3970025033546418535294097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42346933691161797709803701 3970025033546418535294097)
          ·
            refine ⟨2977518775159813901470573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3970025033546418535294097 2977518775159813901470573)
            ·
              refine ⟨1116569540684930213051465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2977518775159813901470573 1116569540684930213051465)
              ·
                refine ⟨837427155513697659788599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1116569540684930213051465 837427155513697659788599)
                ·
                  refine ⟨1256140733270546489682899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837427155513697659788599 1256140733270546489682899)
                  ·
                    refine ⟨1884211099905819734524349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1256140733270546489682899 1884211099905819734524349)
                    ·
                      refine ⟨706579162464682400446631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1884211099905819734524349 706579162464682400446631)
                      ·
                        rfl

theorem cell23_1376058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_1376058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376058 prefixEnd_1376058 := by exact prefixLift 1376058
  have htrace : WordTrace (prefixWord ++ tailWord_1376058) baseStart_1376058 baseEnd_1376058 := by
    simpa [prefixWord, tailWord_1376058, baseEnd_1376058] using wordTrace_append hprefix tailTrace_1376058
  have hstable : (prefixWord ++ tailWord_1376058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376058).length < 2 ^ (prefixWord ++ tailWord_1376058).sum := by decide
  have hdescent : baseEnd_1376058 < baseStart_1376058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376060 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1376060 : Nat := 118140960795 + 1376060 * 2 ^ 59
def prefixEnd_1376060 : Nat := 4983230072969 + 3 ^ 40 * 1376060 * 2
def baseEnd_1376060 : Nat := 706580189425991392621621

theorem tailTrace_1376060 : CollatzResearch.WordTrace tailWord_1376060 prefixEnd_1376060 706580189425991392621621 := by
  unfold tailWord_1376060
  simp only [CollatzResearch.WordTrace]
  refine ⟨25094515697388553591410817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33459354263184738121881089 25094515697388553591410817)
  ·
    refine ⟨18820886773041415193558113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25094515697388553591410817 18820886773041415193558113)
    ·
      refine ⟨14115665079781061395168585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18820886773041415193558113 14115665079781061395168585)
      ·
        refine ⟨10586748809835796046376439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14115665079781061395168585 10586748809835796046376439)
        ·
          refine ⟨15880123214753694069564659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10586748809835796046376439 15880123214753694069564659)
          ·
            refine ⟨23820184822130541104346989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15880123214753694069564659 23820184822130541104346989)
            ·
              refine ⟨8932569308298952914130121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23820184822130541104346989 8932569308298952914130121)
              ·
                refine ⟨6699426981224214685597591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8932569308298952914130121 6699426981224214685597591)
                ·
                  refine ⟨10049140471836322028396387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6699426981224214685597591 10049140471836322028396387)
                  ·
                    refine ⟨15073710707754483042594581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10049140471836322028396387 15073710707754483042594581)
                    ·
                      refine ⟨706580189425991392621621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15073710707754483042594581 706580189425991392621621)
                      ·
                        rfl

theorem cell23_1376060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1376060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376060 prefixEnd_1376060 := by exact prefixLift 1376060
  have htrace : WordTrace (prefixWord ++ tailWord_1376060) baseStart_1376060 baseEnd_1376060 := by
    simpa [prefixWord, tailWord_1376060, baseEnd_1376060] using wordTrace_append hprefix tailTrace_1376060
  have hstable : (prefixWord ++ tailWord_1376060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376060).length < 2 ^ (prefixWord ++ tailWord_1376060).sum := by decide
  have hdescent : baseEnd_1376060 < baseStart_1376060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376084 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1376084 : Nat := 118140960795 + 1376084 * 2 ^ 59
def prefixEnd_1376084 : Nat := 4983230072969 + 3 ^ 40 * 1376084 * 2
def baseEnd_1376084 : Nat := 706592512961699298721511

theorem tailTrace_1376084 : CollatzResearch.WordTrace tailWord_1376084 prefixEnd_1376084 706592512961699298721511 := by
  unfold tailWord_1376084
  simp only [CollatzResearch.WordTrace]
  refine ⟨25094953373345079640847653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33459937831126772854463537 25094953373345079640847653)
  ·
    refine ⟨4705303757502202432658935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25094953373345079640847653 4705303757502202432658935)
    ·
      refine ⟨7057955636253303648988403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4705303757502202432658935 7057955636253303648988403)
      ·
        refine ⟨10586933454379955473482605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7057955636253303648988403 10586933454379955473482605)
        ·
          refine ⟨3970100045392483302555977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10586933454379955473482605 3970100045392483302555977)
          ·
            refine ⟨2977575034044362476916983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3970100045392483302555977 2977575034044362476916983)
            ·
              refine ⟨4466362551066543715375475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2977575034044362476916983 4466362551066543715375475)
              ·
                refine ⟨6699543826599815573063213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4466362551066543715375475 6699543826599815573063213)
                ·
                  refine ⟨2512328934974930839898705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6699543826599815573063213 2512328934974930839898705)
                  ·
                    refine ⟨1884246701231198129924029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2512328934974930839898705 1884246701231198129924029)
                    ·
                      refine ⟨706592512961699298721511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1884246701231198129924029 706592512961699298721511)
                      ·
                        rfl

theorem cell23_1376084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1376084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376084 prefixEnd_1376084 := by exact prefixLift 1376084
  have htrace : WordTrace (prefixWord ++ tailWord_1376084) baseStart_1376084 baseEnd_1376084 := by
    simpa [prefixWord, tailWord_1376084, baseEnd_1376084] using wordTrace_append hprefix tailTrace_1376084
  have hstable : (prefixWord ++ tailWord_1376084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376084).length < 2 ^ (prefixWord ++ tailWord_1376084).sum := by decide
  have hdescent : baseEnd_1376084 < baseStart_1376084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376097 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_1376097 : Nat := 118140960795 + 1376097 * 2 ^ 59
def prefixEnd_1376097 : Nat := 4983230072969 + 3 ^ 40 * 1376097 * 2
def baseEnd_1376097 : Nat := 706599188210207747858951

theorem tailTrace_1376097 : CollatzResearch.WordTrace tailWord_1376097 prefixEnd_1376097 706599188210207747858951 := by
  unfold tailWord_1376097
  simp only [CollatzResearch.WordTrace]
  refine ⟨50190380895643062501918545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33460253930428708334612363 50190380895643062501918545)
  ·
    refine ⟨37642785671732296876438909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50190380895643062501918545 37642785671732296876438909)
    ·
      refine ⟨14116044626899611328664591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37642785671732296876438909 14116044626899611328664591)
      ·
        refine ⟨21174066940349416992996887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14116044626899611328664591 21174066940349416992996887)
        ·
          refine ⟨31761100410524125489495331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21174066940349416992996887 31761100410524125489495331)
          ·
            refine ⟨47641650615786188234242997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31761100410524125489495331 47641650615786188234242997)
            ·
              refine ⟨4466404745229955146960281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47641650615786188234242997 4466404745229955146960281)
              ·
                refine ⟨3349803558922466360220211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4466404745229955146960281 3349803558922466360220211)
                ·
                  refine ⟨5024705338383699540330317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349803558922466360220211 5024705338383699540330317)
                  ·
                    refine ⟨1884264501893887327623869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5024705338383699540330317 1884264501893887327623869)
                    ·
                      refine ⟨706599188210207747858951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1884264501893887327623869 706599188210207747858951)
                      ·
                        rfl

theorem cell23_1376097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_1376097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376097 prefixEnd_1376097 := by exact prefixLift 1376097
  have htrace : WordTrace (prefixWord ++ tailWord_1376097) baseStart_1376097 baseEnd_1376097 := by
    simpa [prefixWord, tailWord_1376097, baseEnd_1376097] using wordTrace_append hprefix tailTrace_1376097
  have hstable : (prefixWord ++ tailWord_1376097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376097).length < 2 ^ (prefixWord ++ tailWord_1376097).sum := by decide
  have hdescent : baseEnd_1376097 < baseStart_1376097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376160 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 11]
def baseStart_1376160 : Nat := 118140960795 + 1376160 * 2 ^ 59
def prefixEnd_1376160 : Nat := 4983230072969 + 3 ^ 40 * 1376160 * 2
def baseEnd_1376160 : Nat := 78514615276826777930129

theorem tailTrace_1376160 : CollatzResearch.WordTrace tailWord_1376160 prefixEnd_1376160 78514615276826777930129 := by
  unfold tailWord_1376160
  simp only [CollatzResearch.WordTrace]
  refine ⟨25096339347207412130730967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33461785796276549507641289 25096339347207412130730967)
  ·
    refine ⟨37644509020811118196096451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25096339347207412130730967 37644509020811118196096451)
    ·
      refine ⟨56466763531216677294144677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37644509020811118196096451 56466763531216677294144677)
      ·
        refine ⟨10587518162103126992652127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56466763531216677294144677 10587518162103126992652127)
        ·
          refine ⟨15881277243154690488978191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10587518162103126992652127 15881277243154690488978191)
          ·
            refine ⟨23821915864732035733467287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15881277243154690488978191 23821915864732035733467287)
            ·
              refine ⟨35732873797098053600200931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23821915864732035733467287 35732873797098053600200931)
              ·
                refine ⟨53599310695647080400301397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35732873797098053600200931 53599310695647080400301397)
                ·
                  refine ⟨78514615276826777930129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 53599310695647080400301397 78514615276826777930129)
                  ·
                    rfl

theorem cell23_1376160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 11].length) (baseStart_1376160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376160 prefixEnd_1376160 := by exact prefixLift 1376160
  have htrace : WordTrace (prefixWord ++ tailWord_1376160) baseStart_1376160 baseEnd_1376160 := by
    simpa [prefixWord, tailWord_1376160, baseEnd_1376160] using wordTrace_append hprefix tailTrace_1376160
  have hstable : (prefixWord ++ tailWord_1376160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376160).length < 2 ^ (prefixWord ++ tailWord_1376160).sum := by decide
  have hdescent : baseEnd_1376160 < baseStart_1376160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376177 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 7]
def baseStart_1376177 : Nat := 118140960795 + 1376177 * 2 ^ 59
def prefixEnd_1376177 : Nat := 4983230072969 + 3 ^ 40 * 1376177 * 2
def baseEnd_1376177 : Nat := 78515585184729714984287

theorem tailTrace_1376177 : CollatzResearch.WordTrace tailWord_1376177 prefixEnd_1376177 78515585184729714984287 := by
  unfold tailWord_1376177
  simp only [CollatzResearch.WordTrace]
  refine ⟨50193298735353236164830785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33462199156902157443220523 50193298735353236164830785)
  ·
    refine ⟨37644974051514927123623089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50193298735353236164830785 37644974051514927123623089)
    ·
      refine ⟨28233730538636195342717317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37644974051514927123623089 28233730538636195342717317)
      ·
        refine ⟨5293824475994286626759497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28233730538636195342717317 5293824475994286626759497)
        ·
          refine ⟨3970368356995714970069623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5293824475994286626759497 3970368356995714970069623)
          ·
            refine ⟨5955552535493572455104435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3970368356995714970069623 5955552535493572455104435)
            ·
              refine ⟨8933328803240358682656653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5955552535493572455104435 8933328803240358682656653)
              ·
                refine ⟨3349998301215134505996245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8933328803240358682656653 3349998301215134505996245)
                ·
                  refine ⟨78515585184729714984287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3349998301215134505996245 78515585184729714984287)
                  ·
                    rfl

theorem cell23_1376177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 7].length) (baseStart_1376177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376177 prefixEnd_1376177 := by exact prefixLift 1376177
  have htrace : WordTrace (prefixWord ++ tailWord_1376177) baseStart_1376177 baseEnd_1376177 := by
    simpa [prefixWord, tailWord_1376177, baseEnd_1376177] using wordTrace_append hprefix tailTrace_1376177
  have hstable : (prefixWord ++ tailWord_1376177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376177).length < 2 ^ (prefixWord ++ tailWord_1376177).sum := by decide
  have hdescent : baseEnd_1376177 < baseStart_1376177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376207 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 2, 5]
def baseStart_1376207 : Nat := 118140960795 + 1376207 * 2 ^ 59
def prefixEnd_1376207 : Nat := 4983230072969 + 3 ^ 40 * 1376207 * 2
def baseEnd_1376207 : Nat := 235551890360734105827815

theorem tailTrace_1376207 : CollatzResearch.WordTrace tailWord_1376207 prefixEnd_1376207 235551890360734105827815 := by
  unfold tailWord_1376207
  simp only [CollatzResearch.WordTrace]
  refine ⟨50194392925244551288422875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33462928616829700858948583 50194392925244551288422875)
  ·
    refine ⟨75291589387866826932634313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50194392925244551288422875 75291589387866826932634313)
    ·
      refine ⟨56468692040900120199475735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75291589387866826932634313 56468692040900120199475735)
      ·
        refine ⟨84703038061350180299213603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56468692040900120199475735 84703038061350180299213603)
        ·
          refine ⟨127054557092025270448820405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84703038061350180299213603 127054557092025270448820405)
          ·
            refine ⟨11911364727377369104576913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127054557092025270448820405 11911364727377369104576913)
            ·
              refine ⟨8933523545533026828432685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11911364727377369104576913 8933523545533026828432685)
              ·
                refine ⟨3350071329574885060662257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8933523545533026828432685 3350071329574885060662257)
                ·
                  refine ⟨2512553497181163795496693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3350071329574885060662257 2512553497181163795496693)
                  ·
                    refine ⟨235551890360734105827815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2512553497181163795496693 235551890360734105827815)
                    ·
                      rfl

theorem cell23_1376207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_1376207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376207 prefixEnd_1376207 := by exact prefixLift 1376207
  have htrace : WordTrace (prefixWord ++ tailWord_1376207) baseStart_1376207 baseEnd_1376207 := by
    simpa [prefixWord, tailWord_1376207, baseEnd_1376207] using wordTrace_append hprefix tailTrace_1376207
  have hstable : (prefixWord ++ tailWord_1376207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376207).length < 2 ^ (prefixWord ++ tailWord_1376207).sum := by decide
  have hdescent : baseEnd_1376207 < baseStart_1376207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376284 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 6]
def baseStart_1376284 : Nat := 118140960795 + 1376284 * 2 ^ 59
def prefixEnd_1376284 : Nat := 4983230072969 + 3 ^ 40 * 1376284 * 2
def baseEnd_1376284 : Nat := 78521689899177612913399

theorem tailTrace_1376284 : CollatzResearch.WordTrace tailWord_1376284 prefixEnd_1376284 78521689899177612913399 := by
  unfold tailWord_1376284
  simp only [CollatzResearch.WordTrace]
  refine ⟨25098600672982796719487953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33464800897310395625983937 25098600672982796719487953)
  ·
    refine ⟨18823950504737097539615965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25098600672982796719487953 18823950504737097539615965)
    ·
      refine ⟨7058981439276411577355987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18823950504737097539615965 7058981439276411577355987)
      ·
        refine ⟨10588472158914617366033981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7058981439276411577355987 10588472158914617366033981)
        ·
          refine ⟨3970677059592981512262743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10588472158914617366033981 3970677059592981512262743)
          ·
            refine ⟨5956015589389472268394115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3970677059592981512262743 5956015589389472268394115)
            ·
              refine ⟨8934023384084208402591173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956015589389472268394115 8934023384084208402591173)
              ·
                refine ⟨1675129384515789075485845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8934023384084208402591173 1675129384515789075485845)
                ·
                  refine ⟨78521689899177612913399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1675129384515789075485845 78521689899177612913399)
                  ·
                    rfl

theorem cell23_1376284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_1376284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376284 prefixEnd_1376284 := by exact prefixLift 1376284
  have htrace : WordTrace (prefixWord ++ tailWord_1376284) baseStart_1376284 baseEnd_1376284 := by
    simpa [prefixWord, tailWord_1376284, baseEnd_1376284] using wordTrace_append hprefix tailTrace_1376284
  have hstable : (prefixWord ++ tailWord_1376284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376284).length < 2 ^ (prefixWord ++ tailWord_1376284).sum := by decide
  have hdescent : baseEnd_1376284 < baseStart_1376284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376287 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1376287 : Nat := 118140960795 + 1376287 * 2 ^ 59
def prefixEnd_1376287 : Nat := 4983230072969 + 3 ^ 40 * 1376287 * 2
def baseEnd_1376287 : Nat := 706696749534562004483077

theorem tailTrace_1376287 : CollatzResearch.WordTrace tailWord_1376287 prefixEnd_1376287 706696749534562004483077 := by
  unfold tailWord_1376287
  simp only [CollatzResearch.WordTrace]
  refine ⟨50197310764954724951335115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33464873843303149967556743 50197310764954724951335115)
  ·
    refine ⟨75295966147432087427002673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50197310764954724951335115 75295966147432087427002673)
    ·
      refine ⟨56471974610574065570252005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75295966147432087427002673 56471974610574065570252005)
      ·
        refine ⟨10588495239482637294422251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56471974610574065570252005 10588495239482637294422251)
        ·
          refine ⟨15882742859223955941633377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10588495239482637294422251 15882742859223955941633377)
          ·
            refine ⟨11912057144417966956225033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15882742859223955941633377 11912057144417966956225033)
            ·
              refine ⟨8934042858313475217168775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11912057144417966956225033 8934042858313475217168775)
              ·
                refine ⟨13401064287470212825753163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8934042858313475217168775 13401064287470212825753163)
                ·
                  refine ⟨20101596431205319238629745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13401064287470212825753163 20101596431205319238629745)
                  ·
                    refine ⟨15076197323403989428972309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20101596431205319238629745 15076197323403989428972309)
                    ·
                      refine ⟨706696749534562004483077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15076197323403989428972309 706696749534562004483077)
                      ·
                        rfl

theorem cell23_1376287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1376287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376287 prefixEnd_1376287 := by exact prefixLift 1376287
  have htrace : WordTrace (prefixWord ++ tailWord_1376287) baseStart_1376287 baseEnd_1376287 := by
    simpa [prefixWord, tailWord_1376287, baseEnd_1376287] using wordTrace_append hprefix tailTrace_1376287
  have hstable : (prefixWord ++ tailWord_1376287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376287).length < 2 ^ (prefixWord ++ tailWord_1376287).sum := by decide
  have hdescent : baseEnd_1376287 < baseStart_1376287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376314 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_1376314 : Nat := 118140960795 + 1376314 * 2 ^ 59
def prefixEnd_1376314 : Nat := 4983230072969 + 3 ^ 40 * 1376314 * 2
def baseEnd_1376314 : Nat := 235570204504077799615151

theorem tailTrace_1376314 : CollatzResearch.WordTrace tailWord_1376314 prefixEnd_1376314 235570204504077799615151 := by
  unfold tailWord_1376314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12549573883964227140641999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33465530357237939041711997 12549573883964227140641999)
  ·
    refine ⟨18824360825946340710962999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12549573883964227140641999 18824360825946340710962999)
    ·
      refine ⟨28236541238919511066444499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18824360825946340710962999 28236541238919511066444499)
      ·
        refine ⟨42354811858379266599666749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28236541238919511066444499 42354811858379266599666749)
        ·
          refine ⟨15883054446892224974875031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42354811858379266599666749 15883054446892224974875031)
          ·
            refine ⟨23824581670338337462312547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15883054446892224974875031 23824581670338337462312547)
            ·
              refine ⟨35736872505507506193468821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23824581670338337462312547 35736872505507506193468821)
              ·
                refine ⟨1675165898695664352818851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35736872505507506193468821 1675165898695664352818851)
                ·
                  refine ⟨2512748848043496529228277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675165898695664352818851 2512748848043496529228277)
                  ·
                    refine ⟨235570204504077799615151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2512748848043496529228277 235570204504077799615151)
                    ·
                      rfl

theorem cell23_1376314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_1376314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376314 prefixEnd_1376314 := by exact prefixLift 1376314
  have htrace : WordTrace (prefixWord ++ tailWord_1376314) baseStart_1376314 baseEnd_1376314 := by
    simpa [prefixWord, tailWord_1376314, baseEnd_1376314] using wordTrace_append hprefix tailTrace_1376314
  have hstable : (prefixWord ++ tailWord_1376314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376314).length < 2 ^ (prefixWord ++ tailWord_1376314).sum := by decide
  have hdescent : baseEnd_1376314 < baseStart_1376314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376364 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_1376364 : Nat := 118140960795 + 1376364 * 2 ^ 59
def prefixEnd_1376364 : Nat := 4983230072969 + 3 ^ 40 * 1376364 * 2
def baseEnd_1376364 : Nat := 706736287544958203220223

theorem tailTrace_1376364 : CollatzResearch.WordTrace tailWord_1376364 prefixEnd_1376364 706736287544958203220223 := by
  unfold tailWord_1376364
  simp only [CollatzResearch.WordTrace]
  refine ⟨25100059592837883550944073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33466746123783844734592097 25100059592837883550944073)
  ·
    refine ⟨18825044694628412663208055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25100059592837883550944073 18825044694628412663208055)
    ·
      refine ⟨28237567041942618994812083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18825044694628412663208055 28237567041942618994812083)
      ·
        refine ⟨42356350562913928492218125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28237567041942618994812083 42356350562913928492218125)
        ·
          refine ⟨15883631461092723184581797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42356350562913928492218125 15883631461092723184581797)
          ·
            refine ⟨2978180898954885597109087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15883631461092723184581797 2978180898954885597109087)
            ·
              refine ⟨4467271348432328395663631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978180898954885597109087 4467271348432328395663631)
              ·
                refine ⟨6700907022648492593495447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467271348432328395663631 6700907022648492593495447)
                ·
                  refine ⟨10051360533972738890243171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6700907022648492593495447 10051360533972738890243171)
                  ·
                    refine ⟨15077040800959108335364757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10051360533972738890243171 15077040800959108335364757)
                    ·
                      refine ⟨706736287544958203220223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15077040800959108335364757 706736287544958203220223)
                      ·
                        rfl

theorem cell23_1376364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_1376364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376364 prefixEnd_1376364 := by exact prefixLift 1376364
  have htrace : WordTrace (prefixWord ++ tailWord_1376364) baseStart_1376364 baseEnd_1376364 := by
    simpa [prefixWord, tailWord_1376364, baseEnd_1376364] using wordTrace_append hprefix tailTrace_1376364
  have hstable : (prefixWord ++ tailWord_1376364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376364).length < 2 ^ (prefixWord ++ tailWord_1376364).sum := by decide
  have hdescent : baseEnd_1376364 < baseStart_1376364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376368 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 3, 2, 2]
def baseStart_1376368 : Nat := 118140960795 + 1376368 * 2 ^ 59
def prefixEnd_1376368 : Nat := 4983230072969 + 3 ^ 40 * 1376368 * 2
def baseEnd_1376368 : Nat := 706738341467576187570205

theorem tailTrace_1376368 : CollatzResearch.WordTrace tailWord_1376368 prefixEnd_1376368 706738341467576187570205 := by
  unfold tailWord_1376368
  simp only [CollatzResearch.WordTrace]
  refine ⟨25100132538830637892516879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33466843385107517190022505 25100132538830637892516879)
  ·
    refine ⟨37650198808245956838775319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25100132538830637892516879 37650198808245956838775319)
    ·
      refine ⟨56475298212368935258162979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37650198808245956838775319 56475298212368935258162979)
      ·
        refine ⟨84712947318553402887244469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56475298212368935258162979 84712947318553402887244469)
        ·
          refine ⟨7941838811114381520679169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84712947318553402887244469 7941838811114381520679169)
          ·
            refine ⟨5956379108335786140509377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7941838811114381520679169 5956379108335786140509377)
            ·
              refine ⟨4467284331251839605382033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5956379108335786140509377 4467284331251839605382033)
              ·
                refine ⟨3350463248438879704036525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4467284331251839605382033 3350463248438879704036525)
                ·
                  refine ⟨1256423718164579889013697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3350463248438879704036525 1256423718164579889013697)
                  ·
                    refine ⟨942317788623434916760273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1256423718164579889013697 942317788623434916760273)
                    ·
                      refine ⟨706738341467576187570205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942317788623434916760273 706738341467576187570205)
                      ·
                        rfl

theorem cell23_1376368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 2, 2].length) (baseStart_1376368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376368 prefixEnd_1376368 := by exact prefixLift 1376368
  have htrace : WordTrace (prefixWord ++ tailWord_1376368) baseStart_1376368 baseEnd_1376368 := by
    simpa [prefixWord, tailWord_1376368, baseEnd_1376368] using wordTrace_append hprefix tailTrace_1376368
  have hstable : (prefixWord ++ tailWord_1376368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376368).length < 2 ^ (prefixWord ++ tailWord_1376368).sum := by decide
  have hdescent : baseEnd_1376368 < baseStart_1376368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376384 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 3]
def baseStart_1376384 : Nat := 118140960795 + 1376384 * 2 ^ 59
def prefixEnd_1376384 : Nat := 4983230072969 + 3 ^ 40 * 1376384 * 2
def baseEnd_1376384 : Nat := 706746557158048124970131

theorem tailTrace_1376384 : CollatzResearch.WordTrace tailWord_1376384 prefixEnd_1376384 706746557158048124970131 := by
  unfold tailWord_1376384
  simp only [CollatzResearch.WordTrace]
  refine ⟨25100424322801655258808103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33467232430402207011744137 25100424322801655258808103)
  ·
    refine ⟨37650636484202482888212155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25100424322801655258808103 37650636484202482888212155)
    ·
      refine ⟨56475954726303724332318233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37650636484202482888212155 56475954726303724332318233)
      ·
        refine ⟨42356966044727793249238675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56475954726303724332318233 42356966044727793249238675)
        ·
          refine ⟨63535449067091689873858013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42356966044727793249238675 63535449067091689873858013)
          ·
            refine ⟨23825793400159383702696755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63535449067091689873858013 23825793400159383702696755)
            ·
              refine ⟨35738690100239075554045133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23825793400159383702696755 35738690100239075554045133)
              ·
                refine ⟨13402008787589653332766925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35738690100239075554045133 13402008787589653332766925)
                ·
                  refine ⟨5025753295346119999787597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13402008787589653332766925 5025753295346119999787597)
                  ·
                    refine ⟨1884657485754794999920349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5025753295346119999787597 1884657485754794999920349)
                    ·
                      refine ⟨706746557158048124970131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1884657485754794999920349 706746557158048124970131)
                      ·
                        rfl

theorem cell23_1376384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_1376384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376384 prefixEnd_1376384 := by exact prefixLift 1376384
  have htrace : WordTrace (prefixWord ++ tailWord_1376384) baseStart_1376384 baseEnd_1376384 := by
    simpa [prefixWord, tailWord_1376384, baseEnd_1376384] using wordTrace_append hprefix tailTrace_1376384
  have hstable : (prefixWord ++ tailWord_1376384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376384).length < 2 ^ (prefixWord ++ tailWord_1376384).sum := by decide
  have hdescent : baseEnd_1376384 < baseStart_1376384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376498 : List Nat := [3, 2, 1, 3, 2, 1, 1, 5, 5]
def baseStart_1376498 : Nat := 118140960795 + 1376498 * 2 ^ 59
def prefixEnd_1376498 : Nat := 4983230072969 + 3 ^ 40 * 1376498 * 2
def baseEnd_1376498 : Nat := 78533899328073408771623

theorem tailTrace_1376498 : CollatzResearch.WordTrace tailWord_1376498 prefixEnd_1376498 78533899328073408771623 := by
  unfold tailWord_1376498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12551251641797576996816537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33470004378126871991510765 12551251641797576996816537)
  ·
    refine ⟨9413438731348182747612403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12551251641797576996816537 9413438731348182747612403)
    ·
      refine ⟨14120158097022274121418605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9413438731348182747612403 14120158097022274121418605)
      ·
        refine ⟨5295059286383352795531977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14120158097022274121418605 5295059286383352795531977)
        ·
          refine ⟨3971294464787514596648983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5295059286383352795531977 3971294464787514596648983)
          ·
            refine ⟨5956941697181271894973475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971294464787514596648983 5956941697181271894973475)
            ·
              refine ⟨8935412545771907842460213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956941697181271894973475 8935412545771907842460213)
              ·
                refine ⟨837694926166116360230645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8935412545771907842460213 837694926166116360230645)
                ·
                  refine ⟨78533899328073408771623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 837694926166116360230645 78533899328073408771623)
                  ·
                    rfl

theorem cell23_1376498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_1376498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376498 prefixEnd_1376498 := by exact prefixLift 1376498
  have htrace : WordTrace (prefixWord ++ tailWord_1376498) baseStart_1376498 baseEnd_1376498 := by
    simpa [prefixWord, tailWord_1376498, baseEnd_1376498] using wordTrace_append hprefix tailTrace_1376498
  have hstable : (prefixWord ++ tailWord_1376498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376498).length < 2 ^ (prefixWord ++ tailWord_1376498).sum := by decide
  have hdescent : baseEnd_1376498 < baseStart_1376498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376504 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_1376504 : Nat := 118140960795 + 1376504 * 2 ^ 59
def prefixEnd_1376504 : Nat := 4983230072969 + 3 ^ 40 * 1376504 * 2
def baseEnd_1376504 : Nat := 706808174836587655469579

theorem tailTrace_1376504 : CollatzResearch.WordTrace tailWord_1376504 prefixEnd_1376504 706808174836587655469579 := by
  unfold tailWord_1376504
  simp only [CollatzResearch.WordTrace]
  refine ⟨25102612702584285505992283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33470150270112380674656377 25102612702584285505992283)
  ·
    refine ⟨37653919053876428258988425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25102612702584285505992283 37653919053876428258988425)
    ·
      refine ⟨28240439290407321194241319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37653919053876428258988425 28240439290407321194241319)
      ·
        refine ⟨42360658935610981791361979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28240439290407321194241319 42360658935610981791361979)
        ·
          refine ⟨63540988403416472687042969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42360658935610981791361979 63540988403416472687042969)
          ·
            refine ⟨47655741302562354515282227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63540988403416472687042969 47655741302562354515282227)
            ·
              refine ⟨71483611953843531772923341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47655741302562354515282227 71483611953843531772923341)
              ·
                refine ⟨26806354482691324414846253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71483611953843531772923341 26806354482691324414846253)
                ·
                  refine ⟨10052382931009246655567345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26806354482691324414846253 10052382931009246655567345)
                  ·
                    refine ⟨7539287198256934991675509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10052382931009246655567345 7539287198256934991675509)
                    ·
                      refine ⟨706808174836587655469579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7539287198256934991675509 706808174836587655469579)
                      ·
                        rfl

theorem cell23_1376504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_1376504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376504 prefixEnd_1376504 := by exact prefixLift 1376504
  have htrace : WordTrace (prefixWord ++ tailWord_1376504) baseStart_1376504 baseEnd_1376504 := by
    simpa [prefixWord, tailWord_1376504, baseEnd_1376504] using wordTrace_append hprefix tailTrace_1376504
  have hstable : (prefixWord ++ tailWord_1376504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376504).length < 2 ^ (prefixWord ++ tailWord_1376504).sum := by decide
  have hdescent : baseEnd_1376504 < baseStart_1376504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376648 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 1, 6]
def baseStart_1376648 : Nat := 118140960795 + 1376648 * 2 ^ 59
def prefixEnd_1376648 : Nat := 4983230072969 + 3 ^ 40 * 1376648 * 2
def baseEnd_1376648 : Nat := 235627372016945030689639

theorem tailTrace_1376648 : CollatzResearch.WordTrace tailWord_1376648 prefixEnd_1376648 235627372016945030689639 := by
  unfold tailWord_1376648
  simp only [CollatzResearch.WordTrace]
  refine ⟨25105238758323441802613299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33473651677764589070151065 25105238758323441802613299)
  ·
    refine ⟨37657858137485162703919949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25105238758323441802613299 37657858137485162703919949)
    ·
      refine ⟨14121696801556936013969981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37657858137485162703919949 14121696801556936013969981)
      ·
        refine ⟨5295636300583851005238743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14121696801556936013969981 5295636300583851005238743)
        ·
          refine ⟨7943454450875776507858115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295636300583851005238743 7943454450875776507858115)
          ·
            refine ⟨11915181676313664761787173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943454450875776507858115 11915181676313664761787173)
            ·
              refine ⟨2234096564308812142835095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11915181676313664761787173 2234096564308812142835095)
              ·
                refine ⟨3351144846463218214252643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234096564308812142835095 3351144846463218214252643)
                ·
                  refine ⟨5026717269694827321378965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351144846463218214252643 5026717269694827321378965)
                  ·
                    refine ⟨235627372016945030689639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5026717269694827321378965 235627372016945030689639)
                    ·
                      rfl

theorem cell23_1376648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_1376648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376648 prefixEnd_1376648 := by exact prefixLift 1376648
  have htrace : WordTrace (prefixWord ++ tailWord_1376648) baseStart_1376648 baseEnd_1376648 := by
    simpa [prefixWord, tailWord_1376648, baseEnd_1376648] using wordTrace_append hprefix tailTrace_1376648
  have hstable : (prefixWord ++ tailWord_1376648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376648).length < 2 ^ (prefixWord ++ tailWord_1376648).sum := by decide
  have hdescent : baseEnd_1376648 < baseStart_1376648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376669 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1376669 : Nat := 118140960795 + 1376669 * 2 ^ 59
def prefixEnd_1376669 : Nat := 4983230072969 + 3 ^ 40 * 1376669 * 2
def baseEnd_1376669 : Nat := 235630966381526503302107

theorem tailTrace_1376669 : CollatzResearch.WordTrace tailWord_1376669 prefixEnd_1376669 235630966381526503302107 := by
  unfold tailWord_1376669
  simp only [CollatzResearch.WordTrace]
  refine ⟨50211243449570804191741061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33474162299713869461160707 50211243449570804191741061)
  ·
    refine ⟨9414608146794525785951449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50211243449570804191741061 9414608146794525785951449)
    ·
      refine ⟨7060956110095894339463587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9414608146794525785951449 7060956110095894339463587)
      ·
        refine ⟨10591434165143841509195381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7060956110095894339463587 10591434165143841509195381)
        ·
          refine ⟨992946952982235141487067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10591434165143841509195381 992946952982235141487067)
          ·
            refine ⟨1489420429473352712230601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992946952982235141487067 1489420429473352712230601)
            ·
              refine ⟨1117065322105014534172951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489420429473352712230601 1117065322105014534172951)
              ·
                refine ⟨1675597983157521801259427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117065322105014534172951 1675597983157521801259427)
                ·
                  refine ⟨2513396974736282701889141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675597983157521801259427 2513396974736282701889141)
                  ·
                    refine ⟨235630966381526503302107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2513396974736282701889141 235630966381526503302107)
                    ·
                      rfl

theorem cell23_1376669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1376669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376669 prefixEnd_1376669 := by exact prefixLift 1376669
  have htrace : WordTrace (prefixWord ++ tailWord_1376669) baseStart_1376669 baseEnd_1376669 := by
    simpa [prefixWord, tailWord_1376669, baseEnd_1376669] using wordTrace_append hprefix tailTrace_1376669
  have hstable : (prefixWord ++ tailWord_1376669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376669).length < 2 ^ (prefixWord ++ tailWord_1376669).sum := by decide
  have hdescent : baseEnd_1376669 < baseStart_1376669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376672 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 1, 1, 4]
def baseStart_1376672 : Nat := 118140960795 + 1376672 * 2 ^ 59
def prefixEnd_1376672 : Nat := 4983230072969 + 3 ^ 40 * 1376672 * 2
def baseEnd_1376672 : Nat := 706894439586542998168807

theorem tailTrace_1376672 : CollatzResearch.WordTrace tailWord_1376672 prefixEnd_1376672 706894439586542998168807 := by
  unfold tailWord_1376672
  simp only [CollatzResearch.WordTrace]
  refine ⟨25105676434279967852050135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33474235245706623802733513 25105676434279967852050135)
  ·
    refine ⟨37658514651419951778075203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25105676434279967852050135 37658514651419951778075203)
    ·
      refine ⟨56487771977129927667112805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37658514651419951778075203 56487771977129927667112805)
      ·
        refine ⟨10591457245711861437583651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56487771977129927667112805 10591457245711861437583651)
        ·
          refine ⟨15887185868567792156375477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10591457245711861437583651 15887185868567792156375477)
          ·
            refine ⟨1489423675178230514660201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15887185868567792156375477 1489423675178230514660201)
            ·
              refine ⟨1117067756383672885995151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489423675178230514660201 1117067756383672885995151)
              ·
                refine ⟨1675601634575509328992727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117067756383672885995151 1675601634575509328992727)
                ·
                  refine ⟨2513402451863263993489091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675601634575509328992727 2513402451863263993489091)
                  ·
                    refine ⟨3770103677794895990233637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2513402451863263993489091 3770103677794895990233637)
                    ·
                      refine ⟨706894439586542998168807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3770103677794895990233637 706894439586542998168807)
                      ·
                        rfl

theorem cell23_1376672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_1376672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376672 prefixEnd_1376672 := by exact prefixLift 1376672
  have htrace : WordTrace (prefixWord ++ tailWord_1376672) baseStart_1376672 baseEnd_1376672 := by
    simpa [prefixWord, tailWord_1376672, baseEnd_1376672] using wordTrace_append hprefix tailTrace_1376672
  have hstable : (prefixWord ++ tailWord_1376672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376672).length < 2 ^ (prefixWord ++ tailWord_1376672).sum := by decide
  have hdescent : baseEnd_1376672 < baseStart_1376672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376675 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 3]
def baseStart_1376675 : Nat := 118140960795 + 1376675 * 2 ^ 59
def prefixEnd_1376675 : Nat := 4983230072969 + 3 ^ 40 * 1376675 * 2
def baseEnd_1376675 : Nat := 706895980028506486431293

theorem tailTrace_1376675 : CollatzResearch.WordTrace tailWord_1376675 prefixEnd_1376675 706895980028506486431293 := by
  unfold tailWord_1376675
  simp only [CollatzResearch.WordTrace]
  refine ⟨50211462287549067216459479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33474308191699378144306319 50211462287549067216459479)
  ·
    refine ⟨75317193431323600824689219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50211462287549067216459479 75317193431323600824689219)
    ·
      refine ⟨112975790146985401237033829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75317193431323600824689219 112975790146985401237033829)
      ·
        refine ⟨21182960652559762731943843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112975790146985401237033829 21182960652559762731943843)
        ·
          refine ⟨31774440978839644097915765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21182960652559762731943843 31774440978839644097915765)
          ·
            refine ⟨2978853841766216634179603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31774440978839644097915765 2978853841766216634179603)
            ·
              refine ⟨4468280762649324951269405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978853841766216634179603 4468280762649324951269405)
              ·
                refine ⟨1675605285993496856726027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4468280762649324951269405 1675605285993496856726027)
                ·
                  refine ⟨2513407928990245285089041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675605285993496856726027 2513407928990245285089041)
                  ·
                    refine ⟨1885055946742683963816781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2513407928990245285089041 1885055946742683963816781)
                    ·
                      refine ⟨706895980028506486431293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1885055946742683963816781 706895980028506486431293)
                      ·
                        rfl

theorem cell23_1376675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_1376675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376675 prefixEnd_1376675 := by exact prefixLift 1376675
  have htrace : WordTrace (prefixWord ++ tailWord_1376675) baseStart_1376675 baseEnd_1376675 := by
    simpa [prefixWord, tailWord_1376675, baseEnd_1376675] using wordTrace_append hprefix tailTrace_1376675
  have hstable : (prefixWord ++ tailWord_1376675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376675).length < 2 ^ (prefixWord ++ tailWord_1376675).sum := by decide
  have hdescent : baseEnd_1376675 < baseStart_1376675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376689 : List Nat := [1, 2, 2, 4, 1, 2, 2, 4, 1, 2, 2]
def baseStart_1376689 : Nat := 118140960795 + 1376689 * 2 ^ 59
def prefixEnd_1376689 : Nat := 4983230072969 + 3 ^ 40 * 1376689 * 2
def baseEnd_1376689 : Nat := 706903168757669431656229

theorem tailTrace_1376689 : CollatzResearch.WordTrace tailWord_1376689 prefixEnd_1376689 706903168757669431656229 := by
  unfold tailWord_1376689
  simp only [CollatzResearch.WordTrace]
  refine ⟨50211972909498347607469121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33474648606332231738312747 50211972909498347607469121)
  ·
    refine ⟨37658979682123760705601841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50211972909498347607469121 37658979682123760705601841)
    ·
      refine ⟨28244234761592820529201381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37658979682123760705601841 28244234761592820529201381)
      ·
        refine ⟨5295794017798653849225259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28244234761592820529201381 5295794017798653849225259)
        ·
          refine ⟨7943691026697980773837889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295794017798653849225259 7943691026697980773837889)
          ·
            refine ⟨5957768270023485580378417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7943691026697980773837889 5957768270023485580378417)
            ·
              refine ⟨4468326202517614185283813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5957768270023485580378417 4468326202517614185283813)
              ·
                refine ⟨837811162972052659740715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4468326202517614185283813 837811162972052659740715)
                ·
                  refine ⟨1256716744458078989611073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837811162972052659740715 1256716744458078989611073)
                  ·
                    refine ⟨942537558343559242208305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1256716744458078989611073 942537558343559242208305)
                    ·
                      refine ⟨706903168757669431656229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942537558343559242208305 706903168757669431656229)
                      ·
                        rfl

theorem cell23_1376689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_1376689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376689 prefixEnd_1376689 := by exact prefixLift 1376689
  have htrace : WordTrace (prefixWord ++ tailWord_1376689) baseStart_1376689 baseEnd_1376689 := by
    simpa [prefixWord, tailWord_1376689, baseEnd_1376689] using wordTrace_append hprefix tailTrace_1376689
  have hstable : (prefixWord ++ tailWord_1376689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376689).length < 2 ^ (prefixWord ++ tailWord_1376689).sum := by decide
  have hdescent : baseEnd_1376689 < baseStart_1376689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376721 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 1, 8]
def baseStart_1376721 : Nat := 118140960795 + 1376721 * 2 ^ 59
def prefixEnd_1376721 : Nat := 4983230072969 + 3 ^ 40 * 1376721 * 2
def baseEnd_1376721 : Nat := 235639866712871102152027

theorem tailTrace_1376721 : CollatzResearch.WordTrace tailWord_1376721 prefixEnd_1376721 235639866712871102152027 := by
  unfold tailWord_1376721
  simp only [CollatzResearch.WordTrace]
  refine ⟨50213140045382417072634017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33475426696921611381756011 50213140045382417072634017)
  ·
    refine ⟨37659855034036812804475513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50213140045382417072634017 37659855034036812804475513)
    ·
      refine ⟨28244891275527609603356635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37659855034036812804475513 28244891275527609603356635)
      ·
        refine ⟨42367336913291414405034953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28244891275527609603356635 42367336913291414405034953)
        ·
          refine ⟨31775502684968560803776215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42367336913291414405034953 31775502684968560803776215)
          ·
            refine ⟨47663254027452841205664323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31775502684968560803776215 47663254027452841205664323)
            ·
              refine ⟨71494881041179261808496485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47663254027452841205664323 71494881041179261808496485)
              ·
                refine ⟨13405290195221111589093091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71494881041179261808496485 13405290195221111589093091)
                ·
                  refine ⟨20107935292831667383639637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13405290195221111589093091 20107935292831667383639637)
                  ·
                    refine ⟨235639866712871102152027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20107935292831667383639637 235639866712871102152027)
                    ·
                      rfl

theorem cell23_1376721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_1376721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376721 prefixEnd_1376721 := by exact prefixLift 1376721
  have htrace : WordTrace (prefixWord ++ tailWord_1376721) baseStart_1376721 baseEnd_1376721 := by
    simpa [prefixWord, tailWord_1376721, baseEnd_1376721] using wordTrace_append hprefix tailTrace_1376721
  have hstable : (prefixWord ++ tailWord_1376721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376721).length < 2 ^ (prefixWord ++ tailWord_1376721).sum := by decide
  have hdescent : baseEnd_1376721 < baseStart_1376721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376748 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_1376748 : Nat := 118140960795 + 1376748 * 2 ^ 59
def prefixEnd_1376748 : Nat := 4983230072969 + 3 ^ 40 * 1376748 * 2
def baseEnd_1376748 : Nat := 706933464116284700818457

theorem tailTrace_1376748 : CollatzResearch.WordTrace tailWord_1376748 prefixEnd_1376748 706933464116284700818457 := by
  unfold tailWord_1376748
  simp only [CollatzResearch.WordTrace]
  refine ⟨25107062408142300341933449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33476083210856400455911265 25107062408142300341933449)
  ·
    refine ⟨18830296806106725256450087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25107062408142300341933449 18830296806106725256450087)
    ·
      refine ⟨28245445209160087884675131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18830296806106725256450087 28245445209160087884675131)
      ·
        refine ⟨42368167813740131827012697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28245445209160087884675131 42368167813740131827012697)
        ·
          refine ⟨31776125860305098870259523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42368167813740131827012697 31776125860305098870259523)
          ·
            refine ⟨47664188790457648305389285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31776125860305098870259523 47664188790457648305389285)
            ·
              refine ⟨8937035398210809057260491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47664188790457648305389285 8937035398210809057260491)
              ·
                refine ⟨13405553097316213585890737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8937035398210809057260491 13405553097316213585890737)
                ·
                  refine ⟨10054164822987160189418053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13405553097316213585890737 10054164822987160189418053)
                  ·
                    refine ⟨1885155904310092535515885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10054164822987160189418053 1885155904310092535515885)
                    ·
                      refine ⟨706933464116284700818457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1885155904310092535515885 706933464116284700818457)
                      ·
                        rfl

theorem cell23_1376748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_1376748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376748 prefixEnd_1376748 := by exact prefixLift 1376748
  have htrace : WordTrace (prefixWord ++ tailWord_1376748) baseStart_1376748 baseEnd_1376748 := by
    simpa [prefixWord, tailWord_1376748, baseEnd_1376748] using wordTrace_append hprefix tailTrace_1376748
  have hstable : (prefixWord ++ tailWord_1376748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376748).length < 2 ^ (prefixWord ++ tailWord_1376748).sum := by decide
  have hdescent : baseEnd_1376748 < baseStart_1376748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376805 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 2, 5, 2]
def baseStart_1376805 : Nat := 118140960795 + 1376805 * 2 ^ 59
def prefixEnd_1376805 : Nat := 4983230072969 + 3 ^ 40 * 1376805 * 2
def baseEnd_1376805 : Nat := 706962732513590977805695

theorem tailTrace_1376805 : CollatzResearch.WordTrace tailWord_1376805 prefixEnd_1376805 706962732513590977805695 := by
  unfold tailWord_1376805
  simp only [CollatzResearch.WordTrace]
  refine ⟨50216203777078099418691869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33477469184718732945794579 50216203777078099418691869)
  ·
    refine ⟨18831076416404287282009451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50216203777078099418691869 18831076416404287282009451)
    ·
      refine ⟨28246614624606430923014177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18831076416404287282009451 28246614624606430923014177)
      ·
        refine ⟨21184960968454823192260633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28246614624606430923014177 21184960968454823192260633)
        ·
          refine ⟨15888720726341117394195475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21184960968454823192260633 15888720726341117394195475)
          ·
            refine ⟨23833081089511676091293213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15888720726341117394195475 23833081089511676091293213)
            ·
              refine ⟨8937405408566878534234955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23833081089511676091293213 8937405408566878534234955)
              ·
                refine ⟨13406108112850317801352433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8937405408566878534234955 13406108112850317801352433)
                ·
                  refine ⟨10054581084637738351014325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13406108112850317801352433 10054581084637738351014325)
                  ·
                    refine ⟨942616976684787970407593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10054581084637738351014325 942616976684787970407593)
                    ·
                      refine ⟨706962732513590977805695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942616976684787970407593 706962732513590977805695)
                      ·
                        rfl

theorem cell23_1376805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_1376805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376805 prefixEnd_1376805 := by exact prefixLift 1376805
  have htrace : WordTrace (prefixWord ++ tailWord_1376805) baseStart_1376805 baseEnd_1376805 := by
    simpa [prefixWord, tailWord_1376805, baseEnd_1376805] using wordTrace_append hprefix tailTrace_1376805
  have hstable : (prefixWord ++ tailWord_1376805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376805).length < 2 ^ (prefixWord ++ tailWord_1376805).sum := by decide
  have hdescent : baseEnd_1376805 < baseStart_1376805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376813 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1376813 : Nat := 118140960795 + 1376813 * 2 ^ 59
def prefixEnd_1376813 : Nat := 4983230072969 + 3 ^ 40 * 1376813 * 2
def baseEnd_1376813 : Nat := 706966840358826946505659

theorem tailTrace_1376813 : CollatzResearch.WordTrace tailWord_1376813 prefixEnd_1376813 706966840358826946505659 := by
  unfold tailWord_1376813
  simp only [CollatzResearch.WordTrace]
  refine ⟨50216495561049116784983093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33477663707366077856655395 50216495561049116784983093)
  ·
    refine ⟨4707796458848354698592165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50216495561049116784983093 4707796458848354698592165)
    ·
      refine ⟨882711836034066505986031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4707796458848354698592165 882711836034066505986031)
      ·
        refine ⟨1324067754051099758979047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882711836034066505986031 1324067754051099758979047)
        ·
          refine ⟨1986101631076649638468571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324067754051099758979047 1986101631076649638468571)
          ·
            refine ⟨2979152446614974457702857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986101631076649638468571 2979152446614974457702857)
            ·
              refine ⟨2234364334961230843277143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2979152446614974457702857 2234364334961230843277143)
              ·
                refine ⟨3351546502441846264915715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234364334961230843277143 3351546502441846264915715)
                ·
                  refine ⟨5027319753662769397373573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351546502441846264915715 5027319753662769397373573)
                  ·
                    refine ⟨942622453811769262007545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5027319753662769397373573 942622453811769262007545)
                    ·
                      refine ⟨706966840358826946505659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942622453811769262007545 706966840358826946505659)
                      ·
                        rfl

theorem cell23_1376813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1376813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376813 prefixEnd_1376813 := by exact prefixLift 1376813
  have htrace : WordTrace (prefixWord ++ tailWord_1376813) baseStart_1376813 baseEnd_1376813 := by
    simpa [prefixWord, tailWord_1376813, baseEnd_1376813] using wordTrace_append hprefix tailTrace_1376813
  have hstable : (prefixWord ++ tailWord_1376813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376813).length < 2 ^ (prefixWord ++ tailWord_1376813).sum := by decide
  have hdescent : baseEnd_1376813 < baseStart_1376813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376852 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_1376852 : Nat := 118140960795 + 1376852 * 2 ^ 59
def prefixEnd_1376852 : Nat := 4983230072969 + 3 ^ 40 * 1376852 * 2
def baseEnd_1376852 : Nat := 706986866104352293917979

theorem tailTrace_1376852 : CollatzResearch.WordTrace tailWord_1376852 prefixEnd_1376852 706986866104352293917979 := by
  unfold tailWord_1376852
  simp only [CollatzResearch.WordTrace]
  refine ⟨25108959003953913222826405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33478612005271884297101873 25108959003953913222826405)
  ·
    refine ⟨4707929813241358729279951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25108959003953913222826405 4707929813241358729279951)
    ·
      refine ⟨7061894719862038093919927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4707929813241358729279951 7061894719862038093919927)
      ·
        refine ⟨10592842079793057140879891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7061894719862038093919927 10592842079793057140879891)
        ·
          refine ⟨15889263119689585711319837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10592842079793057140879891 15889263119689585711319837)
          ·
            refine ⟨5958473669883594641744939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15889263119689585711319837 5958473669883594641744939)
            ·
              refine ⟨8937710504825391962617409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5958473669883594641744939 8937710504825391962617409)
              ·
                refine ⟨6703282878619043971963057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8937710504825391962617409 6703282878619043971963057)
                ·
                  refine ⟨5027462158964282978972293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6703282878619043971963057 5027462158964282978972293)
                  ·
                    refine ⟨942649154805803058557305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5027462158964282978972293 942649154805803058557305)
                    ·
                      refine ⟨706986866104352293917979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942649154805803058557305 706986866104352293917979)
                      ·
                        rfl

theorem cell23_1376852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_1376852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376852 prefixEnd_1376852 := by exact prefixLift 1376852
  have htrace : WordTrace (prefixWord ++ tailWord_1376852) baseStart_1376852 baseEnd_1376852 := by
    simpa [prefixWord, tailWord_1376852, baseEnd_1376852] using wordTrace_append hprefix tailTrace_1376852
  have hstable : (prefixWord ++ tailWord_1376852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376852).length < 2 ^ (prefixWord ++ tailWord_1376852).sum := by decide
  have hdescent : baseEnd_1376852 < baseStart_1376852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376855 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_1376855 : Nat := 118140960795 + 1376855 * 2 ^ 59
def prefixEnd_1376855 : Nat := 4983230072969 + 3 ^ 40 * 1376855 * 2
def baseEnd_1376855 : Nat := 706988406546315782180465

theorem tailTrace_1376855 : CollatzResearch.WordTrace tailWord_1376855 prefixEnd_1376855 706988406546315782180465 := by
  unfold tailWord_1376855
  simp only [CollatzResearch.WordTrace]
  refine ⟨50218027426896957958012019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33478684951264638638674679 50218027426896957958012019)
  ·
    refine ⟨75327041140345436937018029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50218027426896957958012019 75327041140345436937018029)
    ·
      refine ⟨28247640427629538851381761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75327041140345436937018029 28247640427629538851381761)
      ·
        refine ⟨21185730320722154138536321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28247640427629538851381761 21185730320722154138536321)
        ·
          refine ⟨15889297740541615603902241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21185730320722154138536321 15889297740541615603902241)
          ·
            refine ⟨11916973305406211702926681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15889297740541615603902241 11916973305406211702926681)
            ·
              refine ⟨8937729979054658777195011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11916973305406211702926681 8937729979054658777195011)
              ·
                refine ⟨13406594968581988165792517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8937729979054658777195011 13406594968581988165792517)
                ·
                  refine ⟨2513736556609122781086097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13406594968581988165792517 2513736556609122781086097)
                  ·
                    refine ⟨1885302417456842085814573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2513736556609122781086097 1885302417456842085814573)
                    ·
                      refine ⟨706988406546315782180465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1885302417456842085814573 706988406546315782180465)
                      ·
                        rfl

theorem cell23_1376855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_1376855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376855 prefixEnd_1376855 := by exact prefixLift 1376855
  have htrace : WordTrace (prefixWord ++ tailWord_1376855) baseStart_1376855 baseEnd_1376855 := by
    simpa [prefixWord, tailWord_1376855, baseEnd_1376855] using wordTrace_append hprefix tailTrace_1376855
  have hstable : (prefixWord ++ tailWord_1376855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376855).length < 2 ^ (prefixWord ++ tailWord_1376855).sum := by decide
  have hdescent : baseEnd_1376855 < baseStart_1376855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376959 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 1, 1, 4]
def baseStart_1376959 : Nat := 118140960795 + 1376959 * 2 ^ 59
def prefixEnd_1376959 : Nat := 4983230072969 + 3 ^ 40 * 1376959 * 2
def baseEnd_1376959 : Nat := 707041808534383375279987

theorem tailTrace_1376959 : CollatzResearch.WordTrace tailWord_1376959 prefixEnd_1376959 707041808534383375279987 := by
  unfold tailWord_1376959
  simp only [CollatzResearch.WordTrace]
  refine ⟨50221820618520183719797931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33481213745680122479865287 50221820618520183719797931)
  ·
    refine ⟨75332730927780275579696897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50221820618520183719797931 75332730927780275579696897)
    ·
      refine ⟨56499548195835206684772673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75332730927780275579696897 56499548195835206684772673)
      ·
        refine ⟨42374661146876405013579505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56499548195835206684772673 42374661146876405013579505)
        ·
          refine ⟨31780995860157303760184629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42374661146876405013579505 31780995860157303760184629)
          ·
            refine ⟨2979468361889747227517309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31780995860157303760184629 2979468361889747227517309)
            ·
              refine ⟨1117300635708655210318991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2979468361889747227517309 1117300635708655210318991)
              ·
                refine ⟨1675950953562982815478487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117300635708655210318991 1675950953562982815478487)
                ·
                  refine ⟨2513926430344474223217731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675950953562982815478487 2513926430344474223217731)
                  ·
                    refine ⟨3770889645516711334826597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2513926430344474223217731 3770889645516711334826597)
                    ·
                      refine ⟨707041808534383375279987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3770889645516711334826597 707041808534383375279987)
                      ·
                        rfl

theorem cell23_1376959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_1376959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376959 prefixEnd_1376959 := by exact prefixLift 1376959
  have htrace : WordTrace (prefixWord ++ tailWord_1376959) baseStart_1376959 baseEnd_1376959 := by
    simpa [prefixWord, tailWord_1376959, baseEnd_1376959] using wordTrace_append hprefix tailTrace_1376959
  have hstable : (prefixWord ++ tailWord_1376959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376959).length < 2 ^ (prefixWord ++ tailWord_1376959).sum := by decide
  have hdescent : baseEnd_1376959 < baseStart_1376959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376992 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 6, 1, 3]
def baseStart_1376992 : Nat := 118140960795 + 1376992 * 2 ^ 59
def prefixEnd_1376992 : Nat := 4983230072969 + 3 ^ 40 * 1376992 * 2
def baseEnd_1376992 : Nat := 707058753395981746167335

theorem tailTrace_1376992 : CollatzResearch.WordTrace tailWord_1376992 prefixEnd_1376992 707058753395981746167335 := by
  unfold tailWord_1376992
  simp only [CollatzResearch.WordTrace]
  refine ⟨25111512113700315177874615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33482016151600420237166153 25111512113700315177874615)
  ·
    refine ⟨37667268170550472766811923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25111512113700315177874615 37667268170550472766811923)
    ·
      refine ⟨56500902255825709150217885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37667268170550472766811923 56500902255825709150217885)
      ·
        refine ⟨21187838345934640931331707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56500902255825709150217885 21187838345934640931331707)
        ·
          refine ⟨31781757518901961396997561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21187838345934640931331707 31781757518901961396997561)
          ·
            refine ⟨23836318139176471047748171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31781757518901961396997561 23836318139176471047748171)
            ·
              refine ⟨35754477208764706571622257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23836318139176471047748171 35754477208764706571622257)
              ·
                refine ⟨26815857906573529928716693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35754477208764706571622257 26815857906573529928716693)
                ·
                  refine ⟨1256993339370634215408595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26815857906573529928716693 1256993339370634215408595)
                  ·
                    refine ⟨1885490009055951323112893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1256993339370634215408595 1885490009055951323112893)
                    ·
                      refine ⟨707058753395981746167335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1885490009055951323112893 707058753395981746167335)
                      ·
                        rfl

theorem cell23_1376992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_1376992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1376992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1376992 prefixEnd_1376992 := by exact prefixLift 1376992
  have htrace : WordTrace (prefixWord ++ tailWord_1376992) baseStart_1376992 baseEnd_1376992 := by
    simpa [prefixWord, tailWord_1376992, baseEnd_1376992] using wordTrace_append hprefix tailTrace_1376992
  have hstable : (prefixWord ++ tailWord_1376992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376992).length < 2 ^ (prefixWord ++ tailWord_1376992).sum := by decide
  have hdescent : baseEnd_1376992 < baseStart_1376992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377026 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1377026 : Nat := 118140960795 + 1377026 * 2 ^ 59
def prefixEnd_1377026 : Nat := 4983230072969 + 3 ^ 40 * 1377026 * 2
def baseEnd_1377026 : Nat := 707076211738234613142179

theorem tailTrace_1377026 : CollatzResearch.WordTrace tailWord_1377026 prefixEnd_1377026 707076211738234613142179 := by
  unfold tailWord_1377026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12556066077319363540621733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33482842872851636108324621 12556066077319363540621733)
  ·
    refine ⟨2354262389497380663866575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12556066077319363540621733 2354262389497380663866575)
    ·
      refine ⟨3531393584246070995799863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354262389497380663866575 3531393584246070995799863)
      ·
        refine ⟨5297090376369106493699795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531393584246070995799863 5297090376369106493699795)
        ·
          refine ⟨7945635564553659740549693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297090376369106493699795 7945635564553659740549693)
          ·
            refine ⟨2979613336707622402706135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7945635564553659740549693 2979613336707622402706135)
            ·
              refine ⟨4469420005061433604059203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979613336707622402706135 4469420005061433604059203)
              ·
                refine ⟨6704130007592150406088805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4469420005061433604059203 6704130007592150406088805)
                ·
                  refine ⟨1257024376423528201141651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6704130007592150406088805 1257024376423528201141651)
                  ·
                    refine ⟨1885536564635292301712477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1257024376423528201141651 1885536564635292301712477)
                    ·
                      refine ⟨707076211738234613142179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1885536564635292301712477 707076211738234613142179)
                      ·
                        rfl

theorem cell23_1377026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1377026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377026 prefixEnd_1377026 := by exact prefixLift 1377026
  have htrace : WordTrace (prefixWord ++ tailWord_1377026) baseStart_1377026 baseEnd_1377026 := by
    simpa [prefixWord, tailWord_1377026, baseEnd_1377026] using wordTrace_append hprefix tailTrace_1377026
  have hstable : (prefixWord ++ tailWord_1377026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377026).length < 2 ^ (prefixWord ++ tailWord_1377026).sum := by decide
  have hdescent : baseEnd_1377026 < baseStart_1377026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377035 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 5]
def baseStart_1377035 : Nat := 118140960795 + 1377035 * 2 ^ 59
def prefixEnd_1377035 : Nat := 4983230072969 + 3 ^ 40 * 1377035 * 2
def baseEnd_1377035 : Nat := 707080833064125077929637

theorem tailTrace_1377035 : CollatzResearch.WordTrace tailWord_1377035 prefixEnd_1377035 707080833064125077929637 := by
  unfold tailWord_1377035
  simp only [CollatzResearch.WordTrace]
  refine ⟨50224592566244848699564559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33483061710829899133043039 50224592566244848699564559)
  ·
    refine ⟨75336888849367273049346839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50224592566244848699564559 75336888849367273049346839)
    ·
      refine ⟨113005333274050909574020259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75336888849367273049346839 113005333274050909574020259)
      ·
        refine ⟨169507999911076364361030389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113005333274050909574020259 169507999911076364361030389)
        ·
          refine ⟨15891374991663409158846599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169507999911076364361030389 15891374991663409158846599)
          ·
            refine ⟨23837062487495113738269899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15891374991663409158846599 23837062487495113738269899)
            ·
              refine ⟨35755593731242670607404849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23837062487495113738269899 35755593731242670607404849)
              ·
                refine ⟨26816695298432002955553637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35755593731242670607404849 26816695298432002955553637)
                ·
                  refine ⟨5028130368456000554166307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26816695298432002955553637 5028130368456000554166307)
                  ·
                    refine ⟨7542195552684000831249461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5028130368456000554166307 7542195552684000831249461)
                    ·
                      refine ⟨707080833064125077929637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7542195552684000831249461 707080833064125077929637)
                      ·
                        rfl

theorem cell23_1377035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_1377035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377035 prefixEnd_1377035 := by exact prefixLift 1377035
  have htrace : WordTrace (prefixWord ++ tailWord_1377035) baseStart_1377035 baseEnd_1377035 := by
    simpa [prefixWord, tailWord_1377035, baseEnd_1377035] using wordTrace_append hprefix tailTrace_1377035
  have hstable : (prefixWord ++ tailWord_1377035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377035).length < 2 ^ (prefixWord ++ tailWord_1377035).sum := by decide
  have hdescent : baseEnd_1377035 < baseStart_1377035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377094 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1377094 : Nat := 118140960795 + 1377094 * 2 ^ 59
def prefixEnd_1377094 : Nat := 4983230072969 + 3 ^ 40 * 1377094 * 2
def baseEnd_1377094 : Nat := 707111128422740347091867

theorem tailTrace_1377094 : CollatzResearch.WordTrace tailWord_1377094 prefixEnd_1377094 707111128422740347091867 := by
  unfold tailWord_1377094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569585764782221930498823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33484496315354067850641557 1569585764782221930498823)
  ·
    refine ⟨2354378647173332895748235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1569585764782221930498823 2354378647173332895748235)
    ·
      refine ⟨3531567970759999343622353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354378647173332895748235 3531567970759999343622353)
      ·
        refine ⟨2648675978069999507716765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3531567970759999343622353 2648675978069999507716765)
        ·
          refine ⟨993253491776249815393787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2648675978069999507716765 993253491776249815393787)
          ·
            refine ⟨1489880237664374723090681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993253491776249815393787 1489880237664374723090681)
            ·
              refine ⟨1117410178248281042318011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489880237664374723090681 1117410178248281042318011)
              ·
                refine ⟨1676115267372421563477017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117410178248281042318011 1676115267372421563477017)
                ·
                  refine ⟨1257086450529316172607763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676115267372421563477017 1257086450529316172607763)
                  ·
                    refine ⟨1885629675793974258911645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1257086450529316172607763 1885629675793974258911645)
                    ·
                      refine ⟨707111128422740347091867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1885629675793974258911645 707111128422740347091867)
                      ·
                        rfl

theorem cell23_1377094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1377094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377094 prefixEnd_1377094 := by exact prefixLift 1377094
  have htrace : WordTrace (prefixWord ++ tailWord_1377094) baseStart_1377094 baseEnd_1377094 := by
    simpa [prefixWord, tailWord_1377094, baseEnd_1377094] using wordTrace_append hprefix tailTrace_1377094
  have hstable : (prefixWord ++ tailWord_1377094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377094).length < 2 ^ (prefixWord ++ tailWord_1377094).sum := by decide
  have hdescent : baseEnd_1377094 < baseStart_1377094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377100 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 2, 2, 2]
def baseStart_1377100 : Nat := 118140960795 + 1377100 * 2 ^ 59
def prefixEnd_1377100 : Nat := 4983230072969 + 3 ^ 40 * 1377100 * 2
def baseEnd_1377100 : Nat := 707114209306667323616839

theorem tailTrace_1377100 : CollatzResearch.WordTrace tailWord_1377100 prefixEnd_1377100 707114209306667323616839 := by
  unfold tailWord_1377100
  simp only [CollatzResearch.WordTrace]
  refine ⟨25113481655504682400340377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33484642207339576533787169 25113481655504682400340377)
  ·
    refine ⟨18835111241628511800255283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25113481655504682400340377 18835111241628511800255283)
    ·
      refine ⟨28252666862442767700382925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18835111241628511800255283 28252666862442767700382925)
      ·
        refine ⟨10594750073416037887643597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28252666862442767700382925 10594750073416037887643597)
        ·
          refine ⟨3973031277531014207866349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10594750073416037887643597 3973031277531014207866349)
          ·
            refine ⟨1489886729074130327949881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3973031277531014207866349 1489886729074130327949881)
            ·
              refine ⟨1117415046805597745962411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489886729074130327949881 1117415046805597745962411)
              ·
                refine ⟨1676122570208396618943617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117415046805597745962411 1676122570208396618943617)
                ·
                  refine ⟨1257091927656297464207713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676122570208396618943617 1257091927656297464207713)
                  ·
                    refine ⟨942818945742223098155785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1257091927656297464207713 942818945742223098155785)
                    ·
                      refine ⟨707114209306667323616839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942818945742223098155785 707114209306667323616839)
                      ·
                        rfl

theorem cell23_1377100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_1377100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377100 prefixEnd_1377100 := by exact prefixLift 1377100
  have htrace : WordTrace (prefixWord ++ tailWord_1377100) baseStart_1377100 baseEnd_1377100 := by
    simpa [prefixWord, tailWord_1377100, baseEnd_1377100] using wordTrace_append hprefix tailTrace_1377100
  have hstable : (prefixWord ++ tailWord_1377100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377100).length < 2 ^ (prefixWord ++ tailWord_1377100).sum := by decide
  have hdescent : baseEnd_1377100 < baseStart_1377100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377183 : List Nat := [1, 1, 2, 5, 2, 2, 2, 3, 1, 4]
def baseStart_1377183 : Nat := 118140960795 + 1377183 * 2 ^ 59
def prefixEnd_1377183 : Nat := 4983230072969 + 3 ^ 40 * 1377183 * 2
def baseEnd_1377183 : Nat := 235718942733663499626319

theorem tailTrace_1377183 : CollatzResearch.WordTrace tailWord_1377183 prefixEnd_1377183 235718942733663499626319 := by
  unfold tailWord_1377183
  simp only [CollatzResearch.WordTrace]
  refine ⟨50229990569708669975952203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33486660379805779983968135 50229990569708669975952203)
  ·
    refine ⟨75344985854563004963928305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50229990569708669975952203 75344985854563004963928305)
    ·
      refine ⟨56508739390922253722946229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75344985854563004963928305 56508739390922253722946229)
      ·
        refine ⟨5297694317898961286526209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56508739390922253722946229 5297694317898961286526209)
        ·
          refine ⟨3973270738424220964894657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5297694317898961286526209 3973270738424220964894657)
          ·
            refine ⟨2979953053818165723670993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3973270738424220964894657 2979953053818165723670993)
            ·
              refine ⟨2234964790363624292753245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2979953053818165723670993 2234964790363624292753245)
              ·
                refine ⟨838111796386359109782467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2234964790363624292753245 838111796386359109782467)
                ·
                  refine ⟨1257167694579538664673701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838111796386359109782467 1257167694579538664673701)
                  ·
                    refine ⟨235718942733663499626319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1257167694579538664673701 235718942733663499626319)
                    ·
                      rfl

theorem cell23_1377183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 4].length) (baseStart_1377183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377183 prefixEnd_1377183 := by exact prefixLift 1377183
  have htrace : WordTrace (prefixWord ++ tailWord_1377183) baseStart_1377183 baseEnd_1377183 := by
    simpa [prefixWord, tailWord_1377183, baseEnd_1377183] using wordTrace_append hprefix tailTrace_1377183
  have hstable : (prefixWord ++ tailWord_1377183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377183).length < 2 ^ (prefixWord ++ tailWord_1377183).sum := by decide
  have hdescent : baseEnd_1377183 < baseStart_1377183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377232 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_1377232 : Nat := 118140960795 + 1377232 * 2 ^ 59
def prefixEnd_1377232 : Nat := 4983230072969 + 3 ^ 40 * 1377232 * 2
def baseEnd_1377232 : Nat := 707181988753060807166231

theorem tailTrace_1377232 : CollatzResearch.WordTrace tailWord_1377232 prefixEnd_1377232 707181988753060807166231 := by
  unfold tailWord_1377232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25115888873265575672242975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33487851831020767562990633 25115888873265575672242975)
  ·
    refine ⟨37673833309898363508364463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25115888873265575672242975 37673833309898363508364463)
    ·
      refine ⟨56510749964847545262546695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37673833309898363508364463 56510749964847545262546695)
      ·
        refine ⟨84766124947271317893820043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56510749964847545262546695 84766124947271317893820043)
        ·
          refine ⟨127149187420906976840730065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84766124947271317893820043 127149187420906976840730065)
          ·
            refine ⟨95361890565680232630547549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127149187420906976840730065 95361890565680232630547549)
            ·
              refine ⟨35760708962130087236455331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95361890565680232630547549 35760708962130087236455331)
              ·
                refine ⟨53641063443195130854682997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35760708962130087236455331 53641063443195130854682997)
                ·
                  refine ⟨5028849697799543517626531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53641063443195130854682997 5028849697799543517626531)
                  ·
                    refine ⟨7543274546699315276439797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5028849697799543517626531 7543274546699315276439797)
                    ·
                      refine ⟨707181988753060807166231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7543274546699315276439797 707181988753060807166231)
                      ·
                        rfl

theorem cell23_1377232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_1377232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377232 prefixEnd_1377232 := by exact prefixLift 1377232
  have htrace : WordTrace (prefixWord ++ tailWord_1377232) baseStart_1377232 baseEnd_1377232 := by
    simpa [prefixWord, tailWord_1377232, baseEnd_1377232] using wordTrace_append hprefix tailTrace_1377232
  have hstable : (prefixWord ++ tailWord_1377232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377232).length < 2 ^ (prefixWord ++ tailWord_1377232).sum := by decide
  have hdescent : baseEnd_1377232 < baseStart_1377232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377240 : List Nat := [2, 1, 2, 2, 2, 5, 1, 3, 1, 1, 3]
def baseStart_1377240 : Nat := 118140960795 + 1377240 * 2 ^ 59
def prefixEnd_1377240 : Nat := 4983230072969 + 3 ^ 40 * 1377240 * 2
def baseEnd_1377240 : Nat := 707186096598296775866195

theorem tailTrace_1377240 : CollatzResearch.WordTrace tailWord_1377240 prefixEnd_1377240 707186096598296775866195 := by
  unfold tailWord_1377240
  simp only [CollatzResearch.WordTrace]
  refine ⟨25116034765251084355388587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33488046353668112473851449 25116034765251084355388587)
  ·
    refine ⟨37674052147876626533082881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25116034765251084355388587 37674052147876626533082881)
    ·
      refine ⟨28255539110907469899812161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37674052147876626533082881 28255539110907469899812161)
      ·
        refine ⟨21191654333180602424859121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28255539110907469899812161 21191654333180602424859121)
        ·
          refine ⟨15893740749885451818644341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21191654333180602424859121 15893740749885451818644341)
          ·
            refine ⟨1490038195301761107997907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15893740749885451818644341 1490038195301761107997907)
            ·
              refine ⟨2235057292952641661996861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490038195301761107997907 2235057292952641661996861)
              ·
                refine ⟨838146484857240623248823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2235057292952641661996861 838146484857240623248823)
                ·
                  refine ⟨1257219727285860934873235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838146484857240623248823 1257219727285860934873235)
                  ·
                    refine ⟨1885829590928791402309853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1257219727285860934873235 1885829590928791402309853)
                    ·
                      refine ⟨707186096598296775866195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1885829590928791402309853 707186096598296775866195)
                      ·
                        rfl

theorem cell23_1377240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_1377240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377240 prefixEnd_1377240 := by exact prefixLift 1377240
  have htrace : WordTrace (prefixWord ++ tailWord_1377240) baseStart_1377240 baseEnd_1377240 := by
    simpa [prefixWord, tailWord_1377240, baseEnd_1377240] using wordTrace_append hprefix tailTrace_1377240
  have hstable : (prefixWord ++ tailWord_1377240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377240).length < 2 ^ (prefixWord ++ tailWord_1377240).sum := by decide
  have hdescent : baseEnd_1377240 < baseStart_1377240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377249 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_1377249 : Nat := 118140960795 + 1377249 * 2 ^ 59
def prefixEnd_1377249 : Nat := 4983230072969 + 3 ^ 40 * 1377249 * 2
def baseEnd_1377249 : Nat := 707190717924187240653653

theorem tailTrace_1377249 : CollatzResearch.WordTrace tailWord_1377249 prefixEnd_1377249 707190717924187240653653 := by
  unfold tailWord_1377249
  simp only [CollatzResearch.WordTrace]
  refine ⟨50232397787469563247854801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33488265191646375498569867 50232397787469563247854801)
  ·
    refine ⟨37674298340602172435891101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50232397787469563247854801 37674298340602172435891101)
    ·
      refine ⟨14127861877725814663459163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37674298340602172435891101 14127861877725814663459163)
      ·
        refine ⟨21191792816588721995188745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14127861877725814663459163 21191792816588721995188745)
        ·
          refine ⟨15893844612441541496391559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21191792816588721995188745 15893844612441541496391559)
          ·
            refine ⟨23840766918662312244587339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15893844612441541496391559 23840766918662312244587339)
            ·
              refine ⟨35761150377993468366881009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23840766918662312244587339 35761150377993468366881009)
              ·
                refine ⟨26820862783495101275160757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35761150377993468366881009 26820862783495101275160757)
                ·
                  refine ⟨2514455885952665744546321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26820862783495101275160757 2514455885952665744546321)
                  ·
                    refine ⟨1885841914464499308409741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514455885952665744546321 1885841914464499308409741)
                    ·
                      refine ⟨707190717924187240653653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1885841914464499308409741 707190717924187240653653)
                      ·
                        rfl

theorem cell23_1377249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_1377249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377249 prefixEnd_1377249 := by exact prefixLift 1377249
  have htrace : WordTrace (prefixWord ++ tailWord_1377249) baseStart_1377249 baseEnd_1377249 := by
    simpa [prefixWord, tailWord_1377249, baseEnd_1377249] using wordTrace_append hprefix tailTrace_1377249
  have hstable : (prefixWord ++ tailWord_1377249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377249).length < 2 ^ (prefixWord ++ tailWord_1377249).sum := by decide
  have hdescent : baseEnd_1377249 < baseStart_1377249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377250 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_1377250 : Nat := 118140960795 + 1377250 * 2 ^ 59
def prefixEnd_1377250 : Nat := 4983230072969 + 3 ^ 40 * 1377250 * 2
def baseEnd_1377250 : Nat := 707191231404841736741149

theorem tailTrace_1377250 : CollatzResearch.WordTrace tailWord_1377250 prefixEnd_1377250 707191231404841736741149 := by
  unfold tailWord_1377250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12558108565116485104660301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33488289506977293612427469 12558108565116485104660301)
  ·
    refine ⟨4709290711918681914247613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12558108565116485104660301 4709290711918681914247613)
    ·
      refine ⟨1765984016969505717842855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4709290711918681914247613 1765984016969505717842855)
      ·
        refine ⟨2648976025454258576764283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765984016969505717842855 2648976025454258576764283)
        ·
          refine ⟨3973464038181387865146425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648976025454258576764283 3973464038181387865146425)
          ·
            refine ⟨2980098028636040898859819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3973464038181387865146425 2980098028636040898859819)
            ·
              refine ⟨4470147042954061348289729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980098028636040898859819 4470147042954061348289729)
              ·
                refine ⟨3352610282215546011217297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4470147042954061348289729 3352610282215546011217297)
                ·
                  refine ⟨2514457711661659508412973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3352610282215546011217297 2514457711661659508412973)
                  ·
                    refine ⟨942921641873122315654865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514457711661659508412973 942921641873122315654865)
                    ·
                      refine ⟨707191231404841736741149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942921641873122315654865 707191231404841736741149)
                      ·
                        rfl

theorem cell23_1377250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_1377250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377250 prefixEnd_1377250 := by exact prefixLift 1377250
  have htrace : WordTrace (prefixWord ++ tailWord_1377250) baseStart_1377250 baseEnd_1377250 := by
    simpa [prefixWord, tailWord_1377250, baseEnd_1377250] using wordTrace_append hprefix tailTrace_1377250
  have hstable : (prefixWord ++ tailWord_1377250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377250).length < 2 ^ (prefixWord ++ tailWord_1377250).sum := by decide
  have hdescent : baseEnd_1377250 < baseStart_1377250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377263 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 3, 2, 2]
def baseStart_1377263 : Nat := 118140960795 + 1377263 * 2 ^ 59
def prefixEnd_1377263 : Nat := 4983230072969 + 3 ^ 40 * 1377263 * 2
def baseEnd_1377263 : Nat := 707197906653350185878589

theorem tailTrace_1377263 : CollatzResearch.WordTrace tailWord_1377263 prefixEnd_1377263 707197906653350185878589 := by
  unfold tailWord_1377263
  simp only [CollatzResearch.WordTrace]
  refine ⟨50232908409418843638864443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33488605606279229092576295 50232908409418843638864443)
  ·
    refine ⟨75349362614128265458296665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50232908409418843638864443 75349362614128265458296665)
    ·
      refine ⟨56512021960596199093722499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75349362614128265458296665 56512021960596199093722499)
      ·
        refine ⟨84768032940894298640583749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56512021960596199093722499 84768032940894298640583749)
        ·
          refine ⟨15894006176417680995109453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84768032940894298640583749 15894006176417680995109453)
          ·
            refine ⟨5960252316156630373166045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15894006176417680995109453 5960252316156630373166045)
            ·
              refine ⟨2235094618558736389937267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5960252316156630373166045 2235094618558736389937267)
              ·
                refine ⟨3352641927838104584905901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235094618558736389937267 3352641927838104584905901)
                ·
                  refine ⟨1257240722939289219339713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3352641927838104584905901 1257240722939289219339713)
                  ·
                    refine ⟨942930542204466914504785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1257240722939289219339713 942930542204466914504785)
                    ·
                      refine ⟨707197906653350185878589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942930542204466914504785 707197906653350185878589)
                      ·
                        rfl

theorem cell23_1377263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 2, 2].length) (baseStart_1377263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377263 prefixEnd_1377263 := by exact prefixLift 1377263
  have htrace : WordTrace (prefixWord ++ tailWord_1377263) baseStart_1377263 baseEnd_1377263 := by
    simpa [prefixWord, tailWord_1377263, baseEnd_1377263] using wordTrace_append hprefix tailTrace_1377263
  have hstable : (prefixWord ++ tailWord_1377263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377263).length < 2 ^ (prefixWord ++ tailWord_1377263).sum := by decide
  have hdescent : baseEnd_1377263 < baseStart_1377263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377272 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_1377272 : Nat := 118140960795 + 1377272 * 2 ^ 59
def prefixEnd_1377272 : Nat := 4983230072969 + 3 ^ 40 * 1377272 * 2
def baseEnd_1377272 : Nat := 707202527979240650666047

theorem tailTrace_1377272 : CollatzResearch.WordTrace tailWord_1377272 prefixEnd_1377272 707202527979240650666047 := by
  unfold tailWord_1377272
  simp only [CollatzResearch.WordTrace]
  refine ⟨25116618333193119087971035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33488824444257492117294713 25116618333193119087971035)
  ·
    refine ⟨37674927499789678631956553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25116618333193119087971035 37674927499789678631956553)
    ·
      refine ⟨28256195624842258973967415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37674927499789678631956553 28256195624842258973967415)
      ·
        refine ⟨42384293437263388460951123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28256195624842258973967415 42384293437263388460951123)
        ·
          refine ⟨63576440155895082691426685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42384293437263388460951123 63576440155895082691426685)
          ·
            refine ⟨23841165058460656009285007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63576440155895082691426685 23841165058460656009285007)
            ·
              refine ⟨35761747587690984013927511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23841165058460656009285007 35761747587690984013927511)
              ·
                refine ⟨53642621381536476020891267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35761747587690984013927511 53642621381536476020891267)
                ·
                  refine ⟨80463932072304714031336901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53642621381536476020891267 80463932072304714031336901)
                  ·
                    refine ⟨15086987263557133880875669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80463932072304714031336901 15086987263557133880875669)
                    ·
                      refine ⟨707202527979240650666047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15086987263557133880875669 707202527979240650666047)
                      ·
                        rfl

theorem cell23_1377272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_1377272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377272 prefixEnd_1377272 := by exact prefixLift 1377272
  have htrace : WordTrace (prefixWord ++ tailWord_1377272) baseStart_1377272 baseEnd_1377272 := by
    simpa [prefixWord, tailWord_1377272, baseEnd_1377272] using wordTrace_append hprefix tailTrace_1377272
  have hstable : (prefixWord ++ tailWord_1377272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377272).length < 2 ^ (prefixWord ++ tailWord_1377272).sum := by decide
  have hdescent : baseEnd_1377272 < baseStart_1377272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377313 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_1377313 : Nat := 118140960795 + 1377313 * 2 ^ 59
def prefixEnd_1377313 : Nat := 4983230072969 + 3 ^ 40 * 1377313 * 2
def baseEnd_1377313 : Nat := 707223580686074990253359

theorem tailTrace_1377313 : CollatzResearch.WordTrace tailWord_1377313 prefixEnd_1377313 707223580686074990253359 := by
  unfold tailWord_1377313
  simp only [CollatzResearch.WordTrace]
  refine ⟨50234732059237702178184593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33489821372825134785456395 50234732059237702178184593)
  ·
    refine ⟨37676049044428276633638445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50234732059237702178184593 37676049044428276633638445)
    ·
      refine ⟨14128518391660603737614417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37676049044428276633638445 14128518391660603737614417)
      ·
        refine ⟨10596388793745452803210813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14128518391660603737614417 10596388793745452803210813)
        ·
          refine ⟨3973645797654544801204055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10596388793745452803210813 3973645797654544801204055)
          ·
            refine ⟨5960468696481817201806083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973645797654544801204055 5960468696481817201806083)
            ·
              refine ⟨8940703044722725802709125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5960468696481817201806083 8940703044722725802709125)
              ·
                refine ⟨1676381820885511088007961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8940703044722725802709125 1676381820885511088007961)
                ·
                  refine ⟨1257286365664133316005971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676381820885511088007961 1257286365664133316005971)
                  ·
                    refine ⟨1885929548496199974008957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1257286365664133316005971 1885929548496199974008957)
                    ·
                      refine ⟨707223580686074990253359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1885929548496199974008957 707223580686074990253359)
                      ·
                        rfl

theorem cell23_1377313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_1377313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377313 prefixEnd_1377313 := by exact prefixLift 1377313
  have htrace : WordTrace (prefixWord ++ tailWord_1377313) baseStart_1377313 baseEnd_1377313 := by
    simpa [prefixWord, tailWord_1377313, baseEnd_1377313] using wordTrace_append hprefix tailTrace_1377313
  have hstable : (prefixWord ++ tailWord_1377313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377313).length < 2 ^ (prefixWord ++ tailWord_1377313).sum := by decide
  have hdescent : baseEnd_1377313 < baseStart_1377313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377314 : List Nat := [3, 3, 1, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_1377314 : Nat := 118140960795 + 1377314 * 2 ^ 59
def prefixEnd_1377314 : Nat := 4983230072969 + 3 ^ 40 * 1377314 * 2
def baseEnd_1377314 : Nat := 707224094166729486340855

theorem tailTrace_1377314 : CollatzResearch.WordTrace tailWord_1377314 prefixEnd_1377314 707224094166729486340855 := by
  unfold tailWord_1377314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12558692133058519837242749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33489845688156052899313997 12558692133058519837242749)
  ·
    refine ⟨4709509549896944938966031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12558692133058519837242749 4709509549896944938966031)
    ·
      refine ⟨7064264324845417408449047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4709509549896944938966031 7064264324845417408449047)
      ·
        refine ⟨10596396487268126112673571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7064264324845417408449047 10596396487268126112673571)
        ·
          refine ⟨15894594730902189169010357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10596396487268126112673571 15894594730902189169010357)
          ·
            refine ⟨1490118256022080234594721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15894594730902189169010357 1490118256022080234594721)
            ·
              refine ⟨1117588692016560175946041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490118256022080234594721 1117588692016560175946041)
              ·
                refine ⟨838191519012420131959531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117588692016560175946041 838191519012420131959531)
                ·
                  refine ⟨1257287278518630197939297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838191519012420131959531 1257287278518630197939297)
                  ·
                    refine ⟨942965458888972648454473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1257287278518630197939297 942965458888972648454473)
                    ·
                      refine ⟨707224094166729486340855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942965458888972648454473 707224094166729486340855)
                      ·
                        rfl

theorem cell23_1377314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_1377314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377314 prefixEnd_1377314 := by exact prefixLift 1377314
  have htrace : WordTrace (prefixWord ++ tailWord_1377314) baseStart_1377314 baseEnd_1377314 := by
    simpa [prefixWord, tailWord_1377314, baseEnd_1377314] using wordTrace_append hprefix tailTrace_1377314
  have hstable : (prefixWord ++ tailWord_1377314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377314).length < 2 ^ (prefixWord ++ tailWord_1377314).sum := by decide
  have hdescent : baseEnd_1377314 < baseStart_1377314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377329 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 2, 6]
def baseStart_1377329 : Nat := 118140960795 + 1377329 * 2 ^ 59
def prefixEnd_1377329 : Nat := 4983230072969 + 3 ^ 40 * 1377329 * 2
def baseEnd_1377329 : Nat := 235743932125515642551095

theorem tailTrace_1377329 : CollatzResearch.WordTrace tailWord_1377329 prefixEnd_1377329 235743932125515642551095 := by
  unfold tailWord_1377329
  simp only [CollatzResearch.WordTrace]
  refine ⟨50235315627179736910767041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33490210418119824607178027 50235315627179736910767041)
  ·
    refine ⟨37676486720384802683075281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50235315627179736910767041 37676486720384802683075281)
    ·
      refine ⟨28257365040288602012306461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37676486720384802683075281 28257365040288602012306461)
      ·
        refine ⟨10596511890108225754614923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28257365040288602012306461 10596511890108225754614923)
        ·
          refine ⟨15894767835162338631922385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10596511890108225754614923 15894767835162338631922385)
          ·
            refine ⟨11921075876371753973941789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15894767835162338631922385 11921075876371753973941789)
            ·
              refine ⟨4470403453639407740228171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11921075876371753973941789 4470403453639407740228171)
              ·
                refine ⟨6705605180459111610342257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470403453639407740228171 6705605180459111610342257)
                ·
                  refine ⟨5029203885344333707756693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6705605180459111610342257 5029203885344333707756693)
                  ·
                    refine ⟨235743932125515642551095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5029203885344333707756693 235743932125515642551095)
                    ·
                      rfl

theorem cell23_1377329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_1377329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377329 prefixEnd_1377329 := by exact prefixLift 1377329
  have htrace : WordTrace (prefixWord ++ tailWord_1377329) baseStart_1377329 baseEnd_1377329 := by
    simpa [prefixWord, tailWord_1377329, baseEnd_1377329] using wordTrace_append hprefix tailTrace_1377329
  have hstable : (prefixWord ++ tailWord_1377329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377329).length < 2 ^ (prefixWord ++ tailWord_1377329).sum := by decide
  have hdescent : baseEnd_1377329 < baseStart_1377329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377357 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_1377357 : Nat := 118140960795 + 1377357 * 2 ^ 59
def prefixEnd_1377357 : Nat := 4983230072969 + 3 ^ 40 * 1377357 * 2
def baseEnd_1377357 : Nat := 707246173834872818103157

theorem tailTrace_1377357 : CollatzResearch.WordTrace tailWord_1377357 prefixEnd_1377357 707246173834872818103157 := by
  unfold tailWord_1377357
  simp only [CollatzResearch.WordTrace]
  refine ⟨50236336871078297692786325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33490891247385531795190883 50236336871078297692786325)
  ·
    refine ⟨2354828290831795204349359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50236336871078297692786325 2354828290831795204349359)
    ·
      refine ⟨3532242436247692806524039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354828290831795204349359 3532242436247692806524039)
      ·
        refine ⟨5298363654371539209786059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3532242436247692806524039 5298363654371539209786059)
        ·
          refine ⟨7947545481557308814679089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5298363654371539209786059 7947545481557308814679089)
          ·
            refine ⟨5960659111167981611009317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7947545481557308814679089 5960659111167981611009317)
            ·
              refine ⟨1117623583343996552064247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5960659111167981611009317 1117623583343996552064247)
              ·
                refine ⟨1676435375015994828096371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117623583343996552064247 1676435375015994828096371)
                ·
                  refine ⟨2514653062523992242144557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676435375015994828096371 2514653062523992242144557)
                  ·
                    refine ⟨942994898446497090804209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514653062523992242144557 942994898446497090804209)
                    ·
                      refine ⟨707246173834872818103157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 942994898446497090804209 707246173834872818103157)
                      ·
                        rfl

theorem cell23_1377357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_1377357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377357 prefixEnd_1377357 := by exact prefixLift 1377357
  have htrace : WordTrace (prefixWord ++ tailWord_1377357) baseStart_1377357 baseEnd_1377357 := by
    simpa [prefixWord, tailWord_1377357, baseEnd_1377357] using wordTrace_append hprefix tailTrace_1377357
  have hstable : (prefixWord ++ tailWord_1377357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377357).length < 2 ^ (prefixWord ++ tailWord_1377357).sum := by decide
  have hdescent : baseEnd_1377357 < baseStart_1377357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377376 : List Nat := [2, 1, 1, 3, 2, 2, 1, 6, 5]
def baseStart_1377376 : Nat := 118140960795 + 1377376 * 2 ^ 59
def prefixEnd_1377376 : Nat := 4983230072969 + 3 ^ 40 * 1377376 * 2
def baseEnd_1377376 : Nat := 78583992218589804862841

theorem tailTrace_1377376 : CollatzResearch.WordTrace tailWord_1377376 prefixEnd_1377376 78583992218589804862841 := by
  unfold tailWord_1377376
  simp only [CollatzResearch.WordTrace]
  refine ⟨25118514929004731968863991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33491353238672975958485321 25118514929004731968863991)
  ·
    refine ⟨37677772393507097953295987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25118514929004731968863991 37677772393507097953295987)
    ·
      refine ⟨56516658590260646929943981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37677772393507097953295987 56516658590260646929943981)
      ·
        refine ⟨21193746971347742598728993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56516658590260646929943981 21193746971347742598728993)
        ·
          refine ⟨15895310228510806949046745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21193746971347742598728993 15895310228510806949046745)
          ·
            refine ⟨11921482671383105211785059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15895310228510806949046745 11921482671383105211785059)
            ·
              refine ⟨17882224007074657817677589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11921482671383105211785059 17882224007074657817677589)
              ·
                refine ⟨838229250331624585203637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17882224007074657817677589 838229250331624585203637)
                ·
                  refine ⟨78583992218589804862841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838229250331624585203637 78583992218589804862841)
                  ·
                    rfl

theorem cell23_1377376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 5].length) (baseStart_1377376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377376 prefixEnd_1377376 := by exact prefixLift 1377376
  have htrace : WordTrace (prefixWord ++ tailWord_1377376) baseStart_1377376 baseEnd_1377376 := by
    simpa [prefixWord, tailWord_1377376, baseEnd_1377376] using wordTrace_append hprefix tailTrace_1377376
  have hstable : (prefixWord ++ tailWord_1377376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377376).length < 2 ^ (prefixWord ++ tailWord_1377376).sum := by decide
  have hdescent : baseEnd_1377376 < baseStart_1377376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377429 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1377429 : Nat := 118140960795 + 1377429 * 2 ^ 59
def prefixEnd_1377429 : Nat := 4983230072969 + 3 ^ 40 * 1377429 * 2
def baseEnd_1377429 : Nat := 707283144441996536402825

theorem tailTrace_1377429 : CollatzResearch.WordTrace tailWord_1377429 prefixEnd_1377429 707283144441996536402825 := by
  unfold tailWord_1377429
  simp only [CollatzResearch.WordTrace]
  refine ⟨50238962926817453989407341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33492641951211635992938227 50238962926817453989407341)
  ·
    refine ⟨18839611097556545246027753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50238962926817453989407341 18839611097556545246027753)
    ·
      refine ⟨14129708323167408934520815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18839611097556545246027753 14129708323167408934520815)
      ·
        refine ⟨21194562484751113401781223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14129708323167408934520815 21194562484751113401781223)
        ·
          refine ⟨31791843727126670102671835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21194562484751113401781223 31791843727126670102671835)
          ·
            refine ⟨47687765590690005154007753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31791843727126670102671835 47687765590690005154007753)
            ·
              refine ⟨35765824193017503865505815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47687765590690005154007753 35765824193017503865505815)
              ·
                refine ⟨53648736289526255798258723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35765824193017503865505815 53648736289526255798258723)
                ·
                  refine ⟨80473104434289383697388085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53648736289526255798258723 80473104434289383697388085)
                  ·
                    refine ⟨7544353540714629721630133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80473104434289383697388085 7544353540714629721630133)
                    ·
                      refine ⟨707283144441996536402825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7544353540714629721630133 707283144441996536402825)
                      ·
                        rfl

theorem cell23_1377429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1377429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377429 prefixEnd_1377429 := by exact prefixLift 1377429
  have htrace : WordTrace (prefixWord ++ tailWord_1377429) baseStart_1377429 baseEnd_1377429 := by
    simpa [prefixWord, tailWord_1377429, baseEnd_1377429] using wordTrace_append hprefix tailTrace_1377429
  have hstable : (prefixWord ++ tailWord_1377429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377429).length < 2 ^ (prefixWord ++ tailWord_1377429).sum := by decide
  have hdescent : baseEnd_1377429 < baseStart_1377429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377463 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_1377463 : Nat := 118140960795 + 1377463 * 2 ^ 59
def prefixEnd_1377463 : Nat := 4983230072969 + 3 ^ 40 * 1377463 * 2
def baseEnd_1377463 : Nat := 707300602784249403377669

theorem tailTrace_1377463 : CollatzResearch.WordTrace tailWord_1377463 prefixEnd_1377463 707300602784249403377669 := by
  unfold tailWord_1377463
  simp only [CollatzResearch.WordTrace]
  refine ⟨50240203008694277796145043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33493468672462851864096695 50240203008694277796145043)
  ·
    refine ⟨75360304513041416694217565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50240203008694277796145043 75360304513041416694217565)
    ·
      refine ⟨28260114192390531260331587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75360304513041416694217565 28260114192390531260331587)
      ·
        refine ⟨42390171288585796890497381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28260114192390531260331587 42390171288585796890497381)
        ·
          refine ⟨7948157116609836916968259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42390171288585796890497381 7948157116609836916968259)
          ·
            refine ⟨11922235674914755375452389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7948157116609836916968259 11922235674914755375452389)
            ·
              refine ⟨2235419189046516632897323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11922235674914755375452389 2235419189046516632897323)
              ·
                refine ⟨3353128783569774949345985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235419189046516632897323 3353128783569774949345985)
                ·
                  refine ⟨2514846587677331212009489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3353128783569774949345985 2514846587677331212009489)
                  ·
                    refine ⟨1886134940757998409007117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514846587677331212009489 1886134940757998409007117)
                    ·
                      refine ⟨707300602784249403377669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1886134940757998409007117 707300602784249403377669)
                      ·
                        rfl

theorem cell23_1377463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_1377463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377463 prefixEnd_1377463 := by exact prefixLift 1377463
  have htrace : WordTrace (prefixWord ++ tailWord_1377463) baseStart_1377463 baseEnd_1377463 := by
    simpa [prefixWord, tailWord_1377463, baseEnd_1377463] using wordTrace_append hprefix tailTrace_1377463
  have hstable : (prefixWord ++ tailWord_1377463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377463).length < 2 ^ (prefixWord ++ tailWord_1377463).sum := by decide
  have hdescent : baseEnd_1377463 < baseStart_1377463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377478 : List Nat := [6, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1377478 : Nat := 118140960795 + 1377478 * 2 ^ 59
def prefixEnd_1377478 : Nat := 4983230072969 + 3 ^ 40 * 1377478 * 2
def baseEnd_1377478 : Nat := 78589811666007427187789

theorem tailTrace_1377478 : CollatzResearch.WordTrace tailWord_1377478 prefixEnd_1377478 78589811666007427187789 := by
  unfold tailWord_1377478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570023440738747979935659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33493833402426623571960725 1570023440738747979935659)
  ·
    refine ⟨2355035161108121969903489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1570023440738747979935659 2355035161108121969903489)
    ·
      refine ⟨1766276370831091477427617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2355035161108121969903489 1766276370831091477427617)
      ·
        refine ⟨1324707278123318608070713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1766276370831091477427617 1324707278123318608070713)
        ·
          refine ⟨993530458592488956053035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324707278123318608070713 993530458592488956053035)
          ·
            refine ⟨1490295687888733434079553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993530458592488956053035 1490295687888733434079553)
            ·
              refine ⟨1117721765916550075559665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490295687888733434079553 1117721765916550075559665)
              ·
                refine ⟨838291324437412556669749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117721765916550075559665 838291324437412556669749)
                ·
                  refine ⟨78589811666007427187789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838291324437412556669749 78589811666007427187789)
                  ·
                    rfl

theorem cell23_1377478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1377478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377478 prefixEnd_1377478 := by exact prefixLift 1377478
  have htrace : WordTrace (prefixWord ++ tailWord_1377478) baseStart_1377478 baseEnd_1377478 := by
    simpa [prefixWord, tailWord_1377478, baseEnd_1377478] using wordTrace_append hprefix tailTrace_1377478
  have hstable : (prefixWord ++ tailWord_1377478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377478).length < 2 ^ (prefixWord ++ tailWord_1377478).sum := by decide
  have hdescent : baseEnd_1377478 < baseStart_1377478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377503 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 4, 3, 2]
def baseStart_1377503 : Nat := 118140960795 + 1377503 * 2 ^ 59
def prefixEnd_1377503 : Nat := 4983230072969 + 3 ^ 40 * 1377503 * 2
def baseEnd_1377503 : Nat := 707321142010429246877485

theorem tailTrace_1377503 : CollatzResearch.WordTrace tailWord_1377503 prefixEnd_1377503 707321142010429246877485 := by
  unfold tailWord_1377503
  simp only [CollatzResearch.WordTrace]
  refine ⟨50241661928549364627601163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33494441285699576418400775 50241661928549364627601163)
  ·
    refine ⟨75362492892824046941401745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50241661928549364627601163 75362492892824046941401745)
    ·
      refine ⟨56521869669618035206051309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75362492892824046941401745 56521869669618035206051309)
      ·
        refine ⟨21195701126106763202269241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56521869669618035206051309 21195701126106763202269241)
        ·
          refine ⟨15896775844580072401701931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21195701126106763202269241 15896775844580072401701931)
          ·
            refine ⟨23845163766870108602552897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15896775844580072401701931 23845163766870108602552897)
            ·
              refine ⟨17883872825152581451914673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23845163766870108602552897 17883872825152581451914673)
              ·
                refine ⟨13412904618864436088936005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17883872825152581451914673 13412904618864436088936005)
                ·
                  refine ⟨2514919616037081766675501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13412904618864436088936005 2514919616037081766675501)
                  ·
                    refine ⟨943094856013905662503313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514919616037081766675501 943094856013905662503313)
                    ·
                      refine ⟨707321142010429246877485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943094856013905662503313 707321142010429246877485)
                      ·
                        rfl

theorem cell23_1377503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_1377503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377503 prefixEnd_1377503 := by exact prefixLift 1377503
  have htrace : WordTrace (prefixWord ++ tailWord_1377503) baseStart_1377503 baseEnd_1377503 := by
    simpa [prefixWord, tailWord_1377503, baseEnd_1377503] using wordTrace_append hprefix tailTrace_1377503
  have hstable : (prefixWord ++ tailWord_1377503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377503).length < 2 ^ (prefixWord ++ tailWord_1377503).sum := by decide
  have hdescent : baseEnd_1377503 < baseStart_1377503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377536 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_1377536 : Nat := 118140960795 + 1377536 * 2 ^ 59
def prefixEnd_1377536 : Nat := 4983230072969 + 3 ^ 40 * 1377536 * 2
def baseEnd_1377536 : Nat := 707338086872027617764833

theorem tailTrace_1377536 : CollatzResearch.WordTrace tailWord_1377536 prefixEnd_1377536 707338086872027617764833 := by
  unfold tailWord_1377536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25121432768714905631776231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33495243691619874175701641 25121432768714905631776231)
  ·
    refine ⟨37682149153072358447664347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25121432768714905631776231 37682149153072358447664347)
    ·
      refine ⟨56523223729608537671496521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37682149153072358447664347 56523223729608537671496521)
      ·
        refine ⟨42392417797206403253622391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56523223729608537671496521 42392417797206403253622391)
        ·
          refine ⟨63588626695809604880433587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42392417797206403253622391 63588626695809604880433587)
          ·
            refine ⟨95382940043714407320650381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63588626695809604880433587 95382940043714407320650381)
            ·
              refine ⟨35768602516392902745243893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95382940043714407320650381 35768602516392902745243893)
              ·
                refine ⟨3353306485911834632366615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35768602516392902745243893 3353306485911834632366615)
                ·
                  refine ⟨5029959728867751948549923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353306485911834632366615 5029959728867751948549923)
                  ·
                    refine ⟨7544939593301627922824885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5029959728867751948549923 7544939593301627922824885)
                    ·
                      refine ⟨707338086872027617764833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7544939593301627922824885 707338086872027617764833)
                      ·
                        rfl

theorem cell23_1377536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_1377536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377536 prefixEnd_1377536 := by exact prefixLift 1377536
  have htrace : WordTrace (prefixWord ++ tailWord_1377536) baseStart_1377536 baseEnd_1377536 := by
    simpa [prefixWord, tailWord_1377536, baseEnd_1377536] using wordTrace_append hprefix tailTrace_1377536
  have hstable : (prefixWord ++ tailWord_1377536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377536).length < 2 ^ (prefixWord ++ tailWord_1377536).sum := by decide
  have hdescent : baseEnd_1377536 < baseStart_1377536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377546 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1377546 : Nat := 118140960795 + 1377546 * 2 ^ 59
def prefixEnd_1377546 : Nat := 4983230072969 + 3 ^ 40 * 1377546 * 2
def baseEnd_1377546 : Nat := 707343221678572578639787

theorem tailTrace_1377546 : CollatzResearch.WordTrace tailWord_1377546 prefixEnd_1377546 707343221678572578639787 := by
  unfold tailWord_1377546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12560807566848395742854123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33495486844929055314277661 12560807566848395742854123)
  ·
    refine ⟨18841211350272593614281185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12560807566848395742854123 18841211350272593614281185)
    ·
      refine ⟨14130908512704445210710889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18841211350272593614281185 14130908512704445210710889)
      ·
        refine ⟨10598181384528333908033167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14130908512704445210710889 10598181384528333908033167)
        ·
          refine ⟨15897272076792500862049751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10598181384528333908033167 15897272076792500862049751)
          ·
            refine ⟨23845908115188751293074627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15897272076792500862049751 23845908115188751293074627)
            ·
              refine ⟨35768862172783126939611941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23845908115188751293074627 35768862172783126939611941)
              ·
                refine ⟨6706661657396836301177239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35768862172783126939611941 6706661657396836301177239)
                ·
                  refine ⟨10059992486095254451765859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6706661657396836301177239 10059992486095254451765859)
                  ·
                    refine ⟨15089988729142881677648789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10059992486095254451765859 15089988729142881677648789)
                    ·
                      refine ⟨707343221678572578639787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15089988729142881677648789 707343221678572578639787)
                      ·
                        rfl

theorem cell23_1377546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1377546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377546 prefixEnd_1377546 := by exact prefixLift 1377546
  have htrace : WordTrace (prefixWord ++ tailWord_1377546) baseStart_1377546 baseEnd_1377546 := by
    simpa [prefixWord, tailWord_1377546, baseEnd_1377546] using wordTrace_append hprefix tailTrace_1377546
  have hstable : (prefixWord ++ tailWord_1377546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377546).length < 2 ^ (prefixWord ++ tailWord_1377546).sum := by decide
  have hdescent : baseEnd_1377546 < baseStart_1377546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377573 : List Nat := [1, 3, 1, 2, 4, 1, 4, 7]
def baseStart_1377573 : Nat := 118140960795 + 1377573 * 2 ^ 59
def prefixEnd_1377573 : Nat := 4983230072969 + 3 ^ 40 * 1377573 * 2
def baseEnd_1377573 : Nat := 26198410579860887888969

theorem tailTrace_1377573 : CollatzResearch.WordTrace tailWord_1377573 prefixEnd_1377573 26198410579860887888969 := by
  unfold tailWord_1377573
  simp only [CollatzResearch.WordTrace]
  refine ⟨50244215038295766582649373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33496143358863844388432915 50244215038295766582649373)
  ·
    refine ⟨18841580639360912468493515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50244215038295766582649373 18841580639360912468493515)
    ·
      refine ⟨28262370959041368702740273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18841580639360912468493515 28262370959041368702740273)
      ·
        refine ⟨21196778219281026527055205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28262370959041368702740273 21196778219281026527055205)
        ·
          refine ⟨3974395916115192473822851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21196778219281026527055205 3974395916115192473822851)
          ·
            refine ⟨5961593874172788710734277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3974395916115192473822851 5961593874172788710734277)
            ·
              refine ⟨1117798851407397883262677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5961593874172788710734277 1117798851407397883262677)
              ·
                refine ⟨26198410579860887888969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1117798851407397883262677 26198410579860887888969)
                ·
                  rfl

theorem cell23_1377573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 7].length) (baseStart_1377573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377573 prefixEnd_1377573 := by exact prefixLift 1377573
  have htrace : WordTrace (prefixWord ++ tailWord_1377573) baseStart_1377573 baseEnd_1377573 := by
    simpa [prefixWord, tailWord_1377573, baseEnd_1377573] using wordTrace_append hprefix tailTrace_1377573
  have hstable : (prefixWord ++ tailWord_1377573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377573).length < 2 ^ (prefixWord ++ tailWord_1377573).sum := by decide
  have hdescent : baseEnd_1377573 < baseStart_1377573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377600 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 2, 1, 3]
def baseStart_1377600 : Nat := 118140960795 + 1377600 * 2 ^ 59
def prefixEnd_1377600 : Nat := 4983230072969 + 3 ^ 40 * 1377600 * 2
def baseEnd_1377600 : Nat := 707370949633915367364539

theorem tailTrace_1377600 : CollatzResearch.WordTrace tailWord_1377600 prefixEnd_1377600 707370949633915367364539 := by
  unfold tailWord_1377600
  simp only [CollatzResearch.WordTrace]
  refine ⟨25122599904598975096941127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33496799872798633462588169 25122599904598975096941127)
  ·
    refine ⟨37683899856898462645411691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25122599904598975096941127 37683899856898462645411691)
    ·
      refine ⟨56525849785347693968117537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37683899856898462645411691 56525849785347693968117537)
      ·
        refine ⟨42394387339010770476088153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56525849785347693968117537 42394387339010770476088153)
        ·
          refine ⟨31795790504258077857066115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42394387339010770476088153 31795790504258077857066115)
          ·
            refine ⟨47693685756387116785599173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31795790504258077857066115 47693685756387116785599173)
            ·
              refine ⟨8942566079322584397299845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47693685756387116785599173 8942566079322584397299845)
              ·
                refine ⟨1676731139872984574493721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8942566079322584397299845 1676731139872984574493721)
                ·
                  refine ⟨1257548354904738430870291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676731139872984574493721 1257548354904738430870291)
                  ·
                    refine ⟨1886322532357107646305437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1257548354904738430870291 1886322532357107646305437)
                    ·
                      refine ⟨707370949633915367364539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1886322532357107646305437 707370949633915367364539)
                      ·
                        rfl

theorem cell23_1377600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_1377600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377600 prefixEnd_1377600 := by exact prefixLift 1377600
  have htrace : WordTrace (prefixWord ++ tailWord_1377600) baseStart_1377600 baseEnd_1377600 := by
    simpa [prefixWord, tailWord_1377600, baseEnd_1377600] using wordTrace_append hprefix tailTrace_1377600
  have hstable : (prefixWord ++ tailWord_1377600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377600).length < 2 ^ (prefixWord ++ tailWord_1377600).sum := by decide
  have hdescent : baseEnd_1377600 < baseStart_1377600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377616 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 1, 8]
def baseStart_1377616 : Nat := 118140960795 + 1377616 * 2 ^ 59
def prefixEnd_1377616 : Nat := 4983230072969 + 3 ^ 40 * 1377616 * 2
def baseEnd_1377616 : Nat := 235793055108129101588155

theorem tailTrace_1377616 : CollatzResearch.WordTrace tailWord_1377616 prefixEnd_1377616 235793055108129101588155 := by
  unfold tailWord_1377616
  simp only [CollatzResearch.WordTrace]
  refine ⟨25122891688569992463232351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33497188918093323284309801 25122891688569992463232351)
  ·
    refine ⟨37684337532854988694848527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25122891688569992463232351 37684337532854988694848527)
    ·
      refine ⟨56526506299282483042272791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37684337532854988694848527 56526506299282483042272791)
      ·
        refine ⟨84789759448923724563409187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56526506299282483042272791 84789759448923724563409187)
        ·
          refine ⟨127184639173385586845113781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84789759448923724563409187 127184639173385586845113781)
          ·
            refine ⟨11923559922504898766729417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127184639173385586845113781 11923559922504898766729417)
            ·
              refine ⟨8942669941878674075047063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11923559922504898766729417 8942669941878674075047063)
              ·
                refine ⟨13414004912818011112570595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8942669941878674075047063 13414004912818011112570595)
                ·
                  refine ⟨20121007369227016668855893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13414004912818011112570595 20121007369227016668855893)
                  ·
                    refine ⟨235793055108129101588155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20121007369227016668855893 235793055108129101588155)
                    ·
                      rfl

theorem cell23_1377616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_1377616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377616 prefixEnd_1377616 := by exact prefixLift 1377616
  have htrace : WordTrace (prefixWord ++ tailWord_1377616) baseStart_1377616 baseEnd_1377616 := by
    simpa [prefixWord, tailWord_1377616, baseEnd_1377616] using wordTrace_append hprefix tailTrace_1377616
  have hstable : (prefixWord ++ tailWord_1377616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377616).length < 2 ^ (prefixWord ++ tailWord_1377616).sum := by decide
  have hdescent : baseEnd_1377616 < baseStart_1377616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377644 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 1, 3, 2]
def baseStart_1377644 : Nat := 118140960795 + 1377644 * 2 ^ 59
def prefixEnd_1377644 : Nat := 4983230072969 + 3 ^ 40 * 1377644 * 2
def baseEnd_1377644 : Nat := 707393542782713195214337

theorem tailTrace_1377644 : CollatzResearch.WordTrace tailWord_1377644 prefixEnd_1377644 707393542782713195214337 := by
  unfold tailWord_1377644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25123402310519272854241993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33497869747359030472322657 25123402310519272854241993)
  ·
    refine ⟨18842551732889454640681495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25123402310519272854241993 18842551732889454640681495)
    ·
      refine ⟨28263827599334181961022243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18842551732889454640681495 28263827599334181961022243)
      ·
        refine ⟨42395741399001272941533365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28263827599334181961022243 42395741399001272941533365)
        ·
          refine ⟨3974600756156369338268753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42395741399001272941533365 3974600756156369338268753)
          ·
            refine ⟨2980950567117277003701565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3974600756156369338268753 2980950567117277003701565)
            ·
              refine ⟨1117856462668978876388087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2980950567117277003701565 1117856462668978876388087)
              ·
                refine ⟨1676784694003468314582131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117856462668978876388087 1676784694003468314582131)
                ·
                  refine ⟨2515177041005202471873197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676784694003468314582131 2515177041005202471873197)
                  ·
                    refine ⟨943191390376950926952449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515177041005202471873197 943191390376950926952449)
                    ·
                      refine ⟨707393542782713195214337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943191390376950926952449 707393542782713195214337)
                      ·
                        rfl

theorem cell23_1377644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_1377644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377644 prefixEnd_1377644 := by exact prefixLift 1377644
  have htrace : WordTrace (prefixWord ++ tailWord_1377644) baseStart_1377644 baseEnd_1377644 := by
    simpa [prefixWord, tailWord_1377644, baseEnd_1377644] using wordTrace_append hprefix tailTrace_1377644
  have hstable : (prefixWord ++ tailWord_1377644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377644).length < 2 ^ (prefixWord ++ tailWord_1377644).sum := by decide
  have hdescent : baseEnd_1377644 < baseStart_1377644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377657 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 2, 2, 2]
def baseStart_1377657 : Nat := 118140960795 + 1377657 * 2 ^ 59
def prefixEnd_1377657 : Nat := 4983230072969 + 3 ^ 40 * 1377657 * 2
def baseEnd_1377657 : Nat := 707400218031221644351777

theorem tailTrace_1377657 : CollatzResearch.WordTrace tailWord_1377657 prefixEnd_1377657 707400218031221644351777 := by
  unfold tailWord_1377657
  simp only [CollatzResearch.WordTrace]
  refine ⟨50247278769991448928707225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33498185846660965952471483 50247278769991448928707225)
  ·
    refine ⟨37685459077493586696530419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50247278769991448928707225 37685459077493586696530419)
    ·
      refine ⟨56528188616240380044795629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37685459077493586696530419 56528188616240380044795629)
      ·
        refine ⟨21198070731090142516798361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56528188616240380044795629 21198070731090142516798361)
        ·
          refine ⟨15898553048317606887598771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21198070731090142516798361 15898553048317606887598771)
          ·
            refine ⟨23847829572476410331398157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15898553048317606887598771 23847829572476410331398157)
            ·
              refine ⟨8942936089678653874274309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23847829572476410331398157 8942936089678653874274309)
              ·
                refine ⟨1676800516814747601426433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8942936089678653874274309 1676800516814747601426433)
                ·
                  refine ⟨1257600387611060701069825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676800516814747601426433 1257600387611060701069825)
                  ·
                    refine ⟨943200290708295525802369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1257600387611060701069825 943200290708295525802369)
                    ·
                      refine ⟨707400218031221644351777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943200290708295525802369 707400218031221644351777)
                      ·
                        rfl

theorem cell23_1377657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_1377657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377657 prefixEnd_1377657 := by exact prefixLift 1377657
  have htrace : WordTrace (prefixWord ++ tailWord_1377657) baseStart_1377657 baseEnd_1377657 := by
    simpa [prefixWord, tailWord_1377657, baseEnd_1377657] using wordTrace_append hprefix tailTrace_1377657
  have hstable : (prefixWord ++ tailWord_1377657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377657).length < 2 ^ (prefixWord ++ tailWord_1377657).sum := by decide
  have hdescent : baseEnd_1377657 < baseStart_1377657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377753 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 8]
def baseStart_1377753 : Nat := 118140960795 + 1377753 * 2 ^ 59
def prefixEnd_1377753 : Nat := 4983230072969 + 3 ^ 40 * 1377753 * 2
def baseEnd_1377753 : Nat := 78605501352672585416815

theorem tailTrace_1377753 : CollatzResearch.WordTrace tailWord_1377753 prefixEnd_1377753 78605501352672585416815 := by
  unfold tailWord_1377753
  simp only [CollatzResearch.WordTrace]
  refine ⟨50250780177643657324201913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33500520118429104882801275 50250780177643657324201913)
  ·
    refine ⟨37688085133232742993151435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50250780177643657324201913 37688085133232742993151435)
    ·
      refine ⟨56532127699849114489727153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37688085133232742993151435 56532127699849114489727153)
      ·
        refine ⟨42399095774886835867295365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56532127699849114489727153 42399095774886835867295365)
        ·
          refine ⟨7949830457791281725117881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42399095774886835867295365 7949830457791281725117881)
          ·
            refine ⟨5962372843343461293838411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7949830457791281725117881 5962372843343461293838411)
            ·
              refine ⟨8943559265015191940757617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5962372843343461293838411 8943559265015191940757617)
              ·
                refine ⟨6707669448761393955568213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8943559265015191940757617 6707669448761393955568213)
                ·
                  refine ⟨78605501352672585416815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6707669448761393955568213 78605501352672585416815)
                  ·
                    rfl

theorem cell23_1377753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 8].length) (baseStart_1377753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377753 prefixEnd_1377753 := by exact prefixLift 1377753
  have htrace : WordTrace (prefixWord ++ tailWord_1377753) baseStart_1377753 baseEnd_1377753 := by
    simpa [prefixWord, tailWord_1377753, baseEnd_1377753] using wordTrace_append hprefix tailTrace_1377753
  have hstable : (prefixWord ++ tailWord_1377753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377753).length < 2 ^ (prefixWord ++ tailWord_1377753).sum := by decide
  have hdescent : baseEnd_1377753 < baseStart_1377753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377767 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1377767 : Nat := 118140960795 + 1377767 * 2 ^ 59
def prefixEnd_1377767 : Nat := 4983230072969 + 3 ^ 40 * 1377767 * 2
def baseEnd_1377767 : Nat := 707456700903216213976271

theorem tailTrace_1377767 : CollatzResearch.WordTrace tailWord_1377767 prefixEnd_1377767 707456700903216213976271 := by
  unfold tailWord_1377767
  simp only [CollatzResearch.WordTrace]
  refine ⟨50251290799592937715211555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33500860533061958476807703 50251290799592937715211555)
  ·
    refine ⟨75376936199389406572817333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50251290799592937715211555 75376936199389406572817333)
    ·
      refine ⟨7066587768692756866201625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75376936199389406572817333 7066587768692756866201625)
      ·
        refine ⟨5299940826519567649651219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7066587768692756866201625 5299940826519567649651219)
        ·
          refine ⟨7949911239779351474476829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299940826519567649651219 7949911239779351474476829)
          ·
            refine ⟨2981216714917256802928811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7949911239779351474476829 2981216714917256802928811)
            ·
              refine ⟨4471825072375885204393217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981216714917256802928811 4471825072375885204393217)
              ·
                refine ⟨3353868804281913903294913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4471825072375885204393217 3353868804281913903294913)
                ·
                  refine ⟨2515401603211435427471185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3353868804281913903294913 2515401603211435427471185)
                  ·
                    refine ⟨1886551202408576570603389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2515401603211435427471185 1886551202408576570603389)
                    ·
                      refine ⟨707456700903216213976271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1886551202408576570603389 707456700903216213976271)
                      ·
                        rfl

theorem cell23_1377767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1377767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377767 prefixEnd_1377767 := by exact prefixLift 1377767
  have htrace : WordTrace (prefixWord ++ tailWord_1377767) baseStart_1377767 baseEnd_1377767 := by
    simpa [prefixWord, tailWord_1377767, baseEnd_1377767] using wordTrace_append hprefix tailTrace_1377767
  have hstable : (prefixWord ++ tailWord_1377767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377767).length < 2 ^ (prefixWord ++ tailWord_1377767).sum := by decide
  have hdescent : baseEnd_1377767 < baseStart_1377767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377798 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1377798 : Nat := 118140960795 + 1377798 * 2 ^ 59
def prefixEnd_1377798 : Nat := 4983230072969 + 3 ^ 40 * 1377798 * 2
def baseEnd_1377798 : Nat := 707472618803505592688629

theorem tailTrace_1377798 : CollatzResearch.WordTrace tailWord_1377798 prefixEnd_1377798 707472618803505592688629 := by
  unfold tailWord_1377798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570388170702519687799689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33501614308320420006393365 1570388170702519687799689)
  ·
    refine ⟨1177791128026889765849767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1570388170702519687799689 1177791128026889765849767)
    ·
      refine ⟨1766686692040334648774651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177791128026889765849767 1766686692040334648774651)
      ·
        refine ⟨2650030038060501973161977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766686692040334648774651 2650030038060501973161977)
        ·
          refine ⟨1987522528545376479871483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2650030038060501973161977 1987522528545376479871483)
          ·
            refine ⟨2981283792818064719807225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987522528545376479871483 2981283792818064719807225)
            ·
              refine ⟨2235962844613548539855419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981283792818064719807225 2235962844613548539855419)
              ·
                refine ⟨3353944266920322809783129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235962844613548539855419 3353944266920322809783129)
                ·
                  refine ⟨2515458200190242107337347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3353944266920322809783129 2515458200190242107337347)
                  ·
                    refine ⟨3773187300285363161006021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2515458200190242107337347 3773187300285363161006021)
                    ·
                      refine ⟨707472618803505592688629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3773187300285363161006021 707472618803505592688629)
                      ·
                        rfl

theorem cell23_1377798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1377798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377798 prefixEnd_1377798 := by exact prefixLift 1377798
  have htrace : WordTrace (prefixWord ++ tailWord_1377798) baseStart_1377798 baseEnd_1377798 := by
    simpa [prefixWord, tailWord_1377798, baseEnd_1377798] using wordTrace_append hprefix tailTrace_1377798
  have hstable : (prefixWord ++ tailWord_1377798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377798).length < 2 ^ (prefixWord ++ tailWord_1377798).sum := by decide
  have hdescent : baseEnd_1377798 < baseStart_1377798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377824 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1377824 : Nat := 118140960795 + 1377824 * 2 ^ 59
def prefixEnd_1377824 : Nat := 4983230072969 + 3 ^ 40 * 1377824 * 2
def baseEnd_1377824 : Nat := 707485969300522490963509

theorem tailTrace_1377824 : CollatzResearch.WordTrace tailWord_1377824 prefixEnd_1377824 707485969300522490963509 := by
  unfold tailWord_1377824
  simp only [CollatzResearch.WordTrace]
  refine ⟨25126684880193218225018263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33502246506924290966691017 25126684880193218225018263)
  ·
    refine ⟨37690027320289827337527395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25126684880193218225018263 37690027320289827337527395)
    ·
      refine ⟨56535040980434741006291093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37690027320289827337527395 56535040980434741006291093)
      ·
        refine ⟨2650080045957878484669895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56535040980434741006291093 2650080045957878484669895)
        ·
          refine ⟨3975120068936817727004843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650080045957878484669895 3975120068936817727004843)
          ·
            refine ⟨5962680103405226590507265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975120068936817727004843 5962680103405226590507265)
            ·
              refine ⟨4472010077553919942880449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5962680103405226590507265 4472010077553919942880449)
              ·
                refine ⟨3354007558165439957160337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4472010077553919942880449 3354007558165439957160337)
                ·
                  refine ⟨2515505668624079967870253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3354007558165439957160337 2515505668624079967870253)
                  ·
                    refine ⟨943314625734029987951345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515505668624079967870253 943314625734029987951345)
                    ·
                      refine ⟨707485969300522490963509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943314625734029987951345 707485969300522490963509)
                      ·
                        rfl

theorem cell23_1377824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1377824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377824 prefixEnd_1377824 := by exact prefixLift 1377824
  have htrace : WordTrace (prefixWord ++ tailWord_1377824) baseStart_1377824 baseEnd_1377824 := by
    simpa [prefixWord, tailWord_1377824, baseEnd_1377824] using wordTrace_append hprefix tailTrace_1377824
  have hstable : (prefixWord ++ tailWord_1377824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377824).length < 2 ^ (prefixWord ++ tailWord_1377824).sum := by decide
  have hdescent : baseEnd_1377824 < baseStart_1377824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377847 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 2, 4]
def baseStart_1377847 : Nat := 118140960795 + 1377847 * 2 ^ 59
def prefixEnd_1377847 : Nat := 4983230072969 + 3 ^ 40 * 1377847 * 2
def baseEnd_1377847 : Nat := 235832593118525300325301

theorem tailTrace_1377847 : CollatzResearch.WordTrace tailWord_1377847 prefixEnd_1377847 235832593118525300325301 := by
  unfold tailWord_1377847
  simp only [CollatzResearch.WordTrace]
  refine ⟨50254208639303111378123795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33502805759535407585415863 50254208639303111378123795)
  ·
    refine ⟨75381312958954667067185693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50254208639303111378123795 75381312958954667067185693)
    ·
      refine ⟨28267992359608000150194635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75381312958954667067185693 28267992359608000150194635)
      ·
        refine ⟨42401988539412000225291953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28267992359608000150194635 42401988539412000225291953)
        ·
          refine ⟨31801491404559000168968965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42401988539412000225291953 31801491404559000168968965)
          ·
            refine ⟨5962779638354812531681681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31801491404559000168968965 5962779638354812531681681)
            ·
              refine ⟨4472084728766109398761261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5962779638354812531681681 4472084728766109398761261)
              ·
                refine ⟨1677031773287291024535473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4472084728766109398761261 1677031773287291024535473)
                ·
                  refine ⟨1257773829965468268401605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677031773287291024535473 1257773829965468268401605)
                  ·
                    refine ⟨235832593118525300325301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1257773829965468268401605 235832593118525300325301)
                    ·
                      rfl

theorem cell23_1377847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_1377847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377847 prefixEnd_1377847 := by exact prefixLift 1377847
  have htrace : WordTrace (prefixWord ++ tailWord_1377847) baseStart_1377847 baseEnd_1377847 := by
    simpa [prefixWord, tailWord_1377847, baseEnd_1377847] using wordTrace_append hprefix tailTrace_1377847
  have hstable : (prefixWord ++ tailWord_1377847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377847).length < 2 ^ (prefixWord ++ tailWord_1377847).sum := by decide
  have hdescent : baseEnd_1377847 < baseStart_1377847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377857 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1377857 : Nat := 118140960795 + 1377857 * 2 ^ 59
def prefixEnd_1377857 : Nat := 4983230072969 + 3 ^ 40 * 1377857 * 2
def baseEnd_1377857 : Nat := 707502914162120861850857

theorem tailTrace_1377857 : CollatzResearch.WordTrace tailWord_1377857 prefixEnd_1377857 707502914162120861850857 := by
  unfold tailWord_1377857
  simp only [CollatzResearch.WordTrace]
  refine ⟨50254573369266883085987825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33503048912844588723991883 50254573369266883085987825)
  ·
    refine ⟨37690930026950162314490869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50254573369266883085987825 37690930026950162314490869)
    ·
      refine ⟨3533524690026577716983519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37690930026950162314490869 3533524690026577716983519)
      ·
        refine ⟨5300287035039866575475279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533524690026577716983519 5300287035039866575475279)
        ·
          refine ⟨7950430552559799863212919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300287035039866575475279 7950430552559799863212919)
          ·
            refine ⟨11925645828839699794819379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950430552559799863212919 11925645828839699794819379)
            ·
              refine ⟨17888468743259549692229069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925645828839699794819379 17888468743259549692229069)
              ·
                refine ⟨6708175778722331134585901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17888468743259549692229069 6708175778722331134585901)
                ·
                  refine ⟨2515565917020874175469713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6708175778722331134585901 2515565917020874175469713)
                  ·
                    refine ⟨1886674437765655631602285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2515565917020874175469713 1886674437765655631602285)
                    ·
                      refine ⟨707502914162120861850857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1886674437765655631602285 707502914162120861850857)
                      ·
                        rfl

theorem cell23_1377857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1377857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377857 prefixEnd_1377857 := by exact prefixLift 1377857
  have htrace : WordTrace (prefixWord ++ tailWord_1377857) baseStart_1377857 baseEnd_1377857 := by
    simpa [prefixWord, tailWord_1377857, baseEnd_1377857] using wordTrace_append hprefix tailTrace_1377857
  have hstable : (prefixWord ++ tailWord_1377857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377857).length < 2 ^ (prefixWord ++ tailWord_1377857).sum := by decide
  have hdescent : baseEnd_1377857 < baseStart_1377857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377874 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_1377874 : Nat := 118140960795 + 1377874 * 2 ^ 59
def prefixEnd_1377874 : Nat := 4983230072969 + 3 ^ 40 * 1377874 * 2
def baseEnd_1377874 : Nat := 707511643333247295338279

theorem tailTrace_1377874 : CollatzResearch.WordTrace tailWord_1377874 prefixEnd_1377874 707511643333247295338279 := by
  unfold tailWord_1377874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12563798352551323747339169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33503462273470196659571117 12563798352551323747339169)
  ·
    refine ⟨9422848764413492810504377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12563798352551323747339169 9422848764413492810504377)
    ·
      refine ⟨7067136573310119607878283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9422848764413492810504377 7067136573310119607878283)
      ·
        refine ⟨10600704859965179411817425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7067136573310119607878283 10600704859965179411817425)
        ·
          refine ⟨7950528644973884558863069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10600704859965179411817425 7950528644973884558863069)
          ·
            refine ⟨2981448241865206709573651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7950528644973884558863069 2981448241865206709573651)
            ·
              refine ⟨4472172362797810064360477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981448241865206709573651 4472172362797810064360477)
              ·
                refine ⟨1677064636049178774135179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4472172362797810064360477 1677064636049178774135179)
                ·
                  refine ⟨2515596954073768161202769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677064636049178774135179 2515596954073768161202769)
                  ·
                    refine ⟨1886697715555326120902077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2515596954073768161202769 1886697715555326120902077)
                    ·
                      refine ⟨707511643333247295338279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1886697715555326120902077 707511643333247295338279)
                      ·
                        rfl

theorem cell23_1377874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_1377874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377874 prefixEnd_1377874 := by exact prefixLift 1377874
  have htrace : WordTrace (prefixWord ++ tailWord_1377874) baseStart_1377874 baseEnd_1377874 := by
    simpa [prefixWord, tailWord_1377874, baseEnd_1377874] using wordTrace_append hprefix tailTrace_1377874
  have hstable : (prefixWord ++ tailWord_1377874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377874).length < 2 ^ (prefixWord ++ tailWord_1377874).sum := by decide
  have hdescent : baseEnd_1377874 < baseStart_1377874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377897 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 5, 3, 2]
def baseStart_1377897 : Nat := 118140960795 + 1377897 * 2 ^ 59
def prefixEnd_1377897 : Nat := 4983230072969 + 3 ^ 40 * 1377897 * 2
def baseEnd_1377897 : Nat := 707523453388300705350673

theorem tailTrace_1377897 : CollatzResearch.WordTrace tailWord_1377897 prefixEnd_1377897 707523453388300705350673 := by
  unfold tailWord_1377897
  simp only [CollatzResearch.WordTrace]
  refine ⟨50256032289121969917443945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33504021526081313278295963 50256032289121969917443945)
  ·
    refine ⟨37692024216841477438082959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50256032289121969917443945 37692024216841477438082959)
    ·
      refine ⟨56538036325262216157124439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37692024216841477438082959 56538036325262216157124439)
      ·
        refine ⟨84807054487893324235686659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56538036325262216157124439 84807054487893324235686659)
        ·
          refine ⟨127210581731839986353529989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84807054487893324235686659 127210581731839986353529989)
          ·
            refine ⟨23851984074719997441286873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127210581731839986353529989 23851984074719997441286873)
            ·
              refine ⟨17888988056039998080965155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23851984074719997441286873 17888988056039998080965155)
              ·
                refine ⟨26833482084059997121447733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17888988056039998080965155 26833482084059997121447733)
                ·
                  refine ⟨2515638945380624730135725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26833482084059997121447733 2515638945380624730135725)
                  ·
                    refine ⟨943364604517734273800897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515638945380624730135725 943364604517734273800897)
                    ·
                      refine ⟨707523453388300705350673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943364604517734273800897 707523453388300705350673)
                      ·
                        rfl

theorem cell23_1377897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 3, 2].length) (baseStart_1377897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377897 prefixEnd_1377897 := by exact prefixLift 1377897
  have htrace : WordTrace (prefixWord ++ tailWord_1377897) baseStart_1377897 baseEnd_1377897 := by
    simpa [prefixWord, tailWord_1377897, baseEnd_1377897] using wordTrace_append hprefix tailTrace_1377897
  have hstable : (prefixWord ++ tailWord_1377897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377897).length < 2 ^ (prefixWord ++ tailWord_1377897).sum := by decide
  have hdescent : baseEnd_1377897 < baseStart_1377897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377901 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_1377901 : Nat := 118140960795 + 1377901 * 2 ^ 59
def prefixEnd_1377901 : Nat := 4983230072969 + 3 ^ 40 * 1377901 * 2
def baseEnd_1377901 : Nat := 707525507310918689700655

theorem tailTrace_1377901 : CollatzResearch.WordTrace tailWord_1377901 prefixEnd_1377901 707525507310918689700655 := by
  unfold tailWord_1377901
  simp only [CollatzResearch.WordTrace]
  refine ⟨50256178181107478600589557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33504118787404985733726371 50256178181107478600589557)
  ·
    refine ⟨4711516704478826118805271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50256178181107478600589557 4711516704478826118805271)
    ·
      refine ⟨7067275056718239178207907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4711516704478826118805271 7067275056718239178207907)
      ·
        refine ⟨10600912585077358767311861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7067275056718239178207907 10600912585077358767311861)
        ·
          refine ⟨993835554851002384435487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10600912585077358767311861 993835554851002384435487)
          ·
            refine ⟨1490753332276503576653231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993835554851002384435487 1490753332276503576653231)
            ·
              refine ⟨2236129998414755364979847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490753332276503576653231 2236129998414755364979847)
              ·
                refine ⟨3354194997622133047469771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236129998414755364979847 3354194997622133047469771)
                ·
                  refine ⟨5031292496433199571204657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354194997622133047469771 5031292496433199571204657)
                  ·
                    refine ⟨3773469372324899678403493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5031292496433199571204657 3773469372324899678403493)
                    ·
                      refine ⟨707525507310918689700655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3773469372324899678403493 707525507310918689700655)
                      ·
                        rfl

theorem cell23_1377901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_1377901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377901 prefixEnd_1377901 := by exact prefixLift 1377901
  have htrace : WordTrace (prefixWord ++ tailWord_1377901) baseStart_1377901 baseEnd_1377901 := by
    simpa [prefixWord, tailWord_1377901, baseEnd_1377901] using wordTrace_append hprefix tailTrace_1377901
  have hstable : (prefixWord ++ tailWord_1377901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377901).length < 2 ^ (prefixWord ++ tailWord_1377901).sum := by decide
  have hdescent : baseEnd_1377901 < baseStart_1377901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377904 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 3]
def baseStart_1377904 : Nat := 118140960795 + 1377904 * 2 ^ 59
def prefixEnd_1377904 : Nat := 4983230072969 + 3 ^ 40 * 1377904 * 2
def baseEnd_1377904 : Nat := 707527047752882177963141

theorem tailTrace_1377904 : CollatzResearch.WordTrace tailWord_1377904 prefixEnd_1377904 707527047752882177963141 := by
  unfold tailWord_1377904
  simp only [CollatzResearch.WordTrace]
  refine ⟨25128143800048305056474383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33504191733397740075299177 25128143800048305056474383)
  ·
    refine ⟨37692215700072457584711575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25128143800048305056474383 37692215700072457584711575)
    ·
      refine ⟨56538323550108686377067363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37692215700072457584711575 56538323550108686377067363)
      ·
        refine ⟨84807485325163029565601045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56538323550108686377067363 84807485325163029565601045)
        ·
          refine ⟨3975350874617017010887549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84807485325163029565601045 3975350874617017010887549)
          ·
            refine ⟨1490756577981381379082831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3975350874617017010887549 1490756577981381379082831)
            ·
              refine ⟨2236134866972072068624247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490756577981381379082831 2236134866972072068624247)
              ·
                refine ⟨3354202300458108102936371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236134866972072068624247 3354202300458108102936371)
                ·
                  refine ⟨5031303450687162154404557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354202300458108102936371 5031303450687162154404557)
                  ·
                    refine ⟨1886738794007685807901709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5031303450687162154404557 1886738794007685807901709)
                    ·
                      refine ⟨707527047752882177963141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1886738794007685807901709 707527047752882177963141)
                      ·
                        rfl

theorem cell23_1377904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 3].length) (baseStart_1377904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377904 prefixEnd_1377904 := by exact prefixLift 1377904
  have htrace : WordTrace (prefixWord ++ tailWord_1377904) baseStart_1377904 baseEnd_1377904 := by
    simpa [prefixWord, tailWord_1377904, baseEnd_1377904] using wordTrace_append hprefix tailTrace_1377904
  have hstable : (prefixWord ++ tailWord_1377904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377904).length < 2 ^ (prefixWord ++ tailWord_1377904).sum := by decide
  have hdescent : baseEnd_1377904 < baseStart_1377904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377987 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 6, 5, 2]
def baseStart_1377987 : Nat := 118140960795 + 1377987 * 2 ^ 59
def prefixEnd_1377987 : Nat := 4983230072969 + 3 ^ 40 * 1377987 * 2
def baseEnd_1377987 : Nat := 707569666647205353225259

theorem tailTrace_1377987 : CollatzResearch.WordTrace tailWord_1377987 prefixEnd_1377987 707569666647205353225259 := by
  unfold tailWord_1377987
  simp only [CollatzResearch.WordTrace]
  refine ⟨50259314858795915288220215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33506209905863943525480143 50259314858795915288220215)
  ·
    refine ⟨75388972288193872932330323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50259314858795915288220215 75388972288193872932330323)
    ·
      refine ⟨113083458432290809398495485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75388972288193872932330323 113083458432290809398495485)
      ·
        refine ⟨42406296912109053524435807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113083458432290809398495485 42406296912109053524435807)
        ·
          refine ⟨63609445368163580286653711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42406296912109053524435807 63609445368163580286653711)
          ·
            refine ⟨95414168052245370429980567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63609445368163580286653711 95414168052245370429980567)
            ·
              refine ⟨143121252078368055644970851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95414168052245370429980567 143121252078368055644970851)
              ·
                refine ⟨214681878117552083467456277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143121252078368055644970851 214681878117552083467456277)
                ·
                  refine ⟨10063213036760253912537013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214681878117552083467456277 10063213036760253912537013)
                  ·
                    refine ⟨943426222196273804300345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10063213036760253912537013 943426222196273804300345)
                    ·
                      refine ⟨707569666647205353225259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943426222196273804300345 707569666647205353225259)
                      ·
                        rfl

theorem cell23_1377987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_1377987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1377987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1377987 prefixEnd_1377987 := by exact prefixLift 1377987
  have htrace : WordTrace (prefixWord ++ tailWord_1377987) baseStart_1377987 baseEnd_1377987 := by
    simpa [prefixWord, tailWord_1377987, baseEnd_1377987] using wordTrace_append hprefix tailTrace_1377987
  have hstable : (prefixWord ++ tailWord_1377987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377987).length < 2 ^ (prefixWord ++ tailWord_1377987).sum := by decide
  have hdescent : baseEnd_1377987 < baseStart_1377987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378001 : List Nat := [1, 2, 2, 1, 2, 6, 2, 2, 5]
def baseStart_1378001 : Nat := 118140960795 + 1378001 * 2 ^ 59
def prefixEnd_1378001 : Nat := 4983230072969 + 3 ^ 40 * 1378001 * 2
def baseEnd_1378001 : Nat := 78619650597374255383355

theorem tailTrace_1378001 : CollatzResearch.WordTrace tailWord_1378001 prefixEnd_1378001 78619650597374255383355 := by
  unfold tailWord_1378001
  simp only [CollatzResearch.WordTrace]
  refine ⟨50259825480745195679229857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33506550320496797119486571 50259825480745195679229857)
  ·
    refine ⟨37694869110558896759422393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50259825480745195679229857 37694869110558896759422393)
    ·
      refine ⟨28271151832919172569566795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37694869110558896759422393 28271151832919172569566795)
      ·
        refine ⟨42406727749378758854350193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28271151832919172569566795 42406727749378758854350193)
        ·
          refine ⟨31805045812034069140762645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42406727749378758854350193 31805045812034069140762645)
          ·
            refine ⟨1490861522439096990973249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31805045812034069140762645 1490861522439096990973249)
            ·
              refine ⟨1118146141829322743229937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490861522439096990973249 1118146141829322743229937)
              ·
                refine ⟨838609606371992057422453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118146141829322743229937 838609606371992057422453)
                ·
                  refine ⟨78619650597374255383355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838609606371992057422453 78619650597374255383355)
                  ·
                    rfl

theorem cell23_1378001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 5].length) (baseStart_1378001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378001 prefixEnd_1378001 := by exact prefixLift 1378001
  have htrace : WordTrace (prefixWord ++ tailWord_1378001) baseStart_1378001 baseEnd_1378001 := by
    simpa [prefixWord, tailWord_1378001, baseEnd_1378001] using wordTrace_append hprefix tailTrace_1378001
  have hstable : (prefixWord ++ tailWord_1378001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378001).length < 2 ^ (prefixWord ++ tailWord_1378001).sum := by decide
  have hdescent : baseEnd_1378001 < baseStart_1378001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378027 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 5, 4]
def baseStart_1378027 : Nat := 118140960795 + 1378027 * 2 ^ 59
def prefixEnd_1378027 : Nat := 4983230072969 + 3 ^ 40 * 1378027 * 2
def baseEnd_1378027 : Nat := 235863401957795065575025

theorem tailTrace_1378027 : CollatzResearch.WordTrace tailWord_1378027 prefixEnd_1378027 235863401957795065575025 := by
  unfold tailWord_1378027
  simp only [CollatzResearch.WordTrace]
  refine ⟨50260773778651002119676335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33507182519100668079784223 50260773778651002119676335)
  ·
    refine ⟨75391160667976503179514503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50260773778651002119676335 75391160667976503179514503)
    ·
      refine ⟨113086741001964754769271755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75391160667976503179514503 113086741001964754769271755)
      ·
        refine ⟨169630111502947132153907633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113086741001964754769271755 169630111502947132153907633)
        ·
          refine ⟨127222583627210349115430725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169630111502947132153907633 127222583627210349115430725)
          ·
            refine ⟨23854234430101940459143261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127222583627210349115430725 23854234430101940459143261)
            ·
              refine ⟨8945337911288227672178723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23854234430101940459143261 8945337911288227672178723)
              ·
                refine ⟨13418006866932341508268085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8945337911288227672178723 13418006866932341508268085)
                ·
                  refine ⟨1257938143774907016400133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13418006866932341508268085 1257938143774907016400133)
                  ·
                    refine ⟨235863401957795065575025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1257938143774907016400133 235863401957795065575025)
                    ·
                      rfl

theorem cell23_1378027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 4].length) (baseStart_1378027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378027 prefixEnd_1378027 := by exact prefixLift 1378027
  have htrace : WordTrace (prefixWord ++ tailWord_1378027) baseStart_1378027 baseEnd_1378027 := by
    simpa [prefixWord, tailWord_1378027, baseEnd_1378027] using wordTrace_append hprefix tailTrace_1378027
  have hstable : (prefixWord ++ tailWord_1378027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378027).length < 2 ^ (prefixWord ++ tailWord_1378027).sum := by decide
  have hdescent : baseEnd_1378027 < baseStart_1378027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378034 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_1378034 : Nat := 118140960795 + 1378034 * 2 ^ 59
def prefixEnd_1378034 : Nat := 4983230072969 + 3 ^ 40 * 1378034 * 2
def baseEnd_1378034 : Nat := 707593800237966669337543

theorem tailTrace_1378034 : CollatzResearch.WordTrace tailWord_1378034 prefixEnd_1378034 707593800237966669337543 := by
  unfold tailWord_1378034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12565257272406410578795289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33507352726417094876787437 12565257272406410578795289)
  ·
    refine ⟨9423942954304807934096467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12565257272406410578795289 9423942954304807934096467)
    ·
      refine ⟨14135914431457211901144701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9423942954304807934096467 14135914431457211901144701)
      ·
        refine ⟨5300967911796454462929263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14135914431457211901144701 5300967911796454462929263)
        ·
          refine ⟨7951451867694681694393895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300967911796454462929263 7951451867694681694393895)
          ·
            refine ⟨11927177801542022541590843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7951451867694681694393895 11927177801542022541590843)
            ·
              refine ⟨17890766702313033812386265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11927177801542022541590843 17890766702313033812386265)
              ·
                refine ⟨13418075026734775359289699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17890766702313033812386265 13418075026734775359289699)
                ·
                  refine ⟨20127112540102163038934549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13418075026734775359289699 20127112540102163038934549)
                  ·
                    refine ⟨943458400317288892450057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20127112540102163038934549 943458400317288892450057)
                    ·
                      refine ⟨707593800237966669337543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943458400317288892450057 707593800237966669337543)
                      ·
                        rfl

theorem cell23_1378034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_1378034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378034 prefixEnd_1378034 := by exact prefixLift 1378034
  have htrace : WordTrace (prefixWord ++ tailWord_1378034) baseStart_1378034 baseEnd_1378034 := by
    simpa [prefixWord, tailWord_1378034, baseEnd_1378034] using wordTrace_append hprefix tailTrace_1378034
  have hstable : (prefixWord ++ tailWord_1378034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378034).length < 2 ^ (prefixWord ++ tailWord_1378034).sum := by decide
  have hdescent : baseEnd_1378034 < baseStart_1378034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378104 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 1, 5]
def baseStart_1378104 : Nat := 118140960795 + 1378104 * 2 ^ 59
def prefixEnd_1378104 : Nat := 4983230072969 + 3 ^ 40 * 1378104 * 2
def baseEnd_1378104 : Nat := 235876581294593798487407

theorem tailTrace_1378104 : CollatzResearch.WordTrace tailWord_1378104 prefixEnd_1378104 235876581294593798487407 := by
  unfold tailWord_1378104
  simp only [CollatzResearch.WordTrace]
  refine ⟨25131791099686022135114683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33509054799581362846819577 25131791099686022135114683)
  ·
    refine ⟨37697686649529033202672025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25131791099686022135114683 37697686649529033202672025)
    ·
      refine ⟨28273264987146774902004019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37697686649529033202672025 28273264987146774902004019)
      ·
        refine ⟨42409897480720162353006029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28273264987146774902004019 42409897480720162353006029)
        ·
          refine ⟨15903711555270060882377261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42409897480720162353006029 15903711555270060882377261)
          ·
            refine ⟨5963891833226272830891473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15903711555270060882377261 5963891833226272830891473)
            ·
              refine ⟨4472918874919704623168605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5963891833226272830891473 4472918874919704623168605)
              ·
                refine ⟨1677344578094889233688227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4472918874919704623168605 1677344578094889233688227)
                ·
                  refine ⟨2516016867142333850532341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677344578094889233688227 2516016867142333850532341)
                  ·
                    refine ⟨235876581294593798487407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2516016867142333850532341 235876581294593798487407)
                    ·
                      rfl

theorem cell23_1378104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_1378104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378104 prefixEnd_1378104 := by exact prefixLift 1378104
  have htrace : WordTrace (prefixWord ++ tailWord_1378104) baseStart_1378104 baseEnd_1378104 := by
    simpa [prefixWord, tailWord_1378104, baseEnd_1378104] using wordTrace_append hprefix tailTrace_1378104
  have hstable : (prefixWord ++ tailWord_1378104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378104).length < 2 ^ (prefixWord ++ tailWord_1378104).sum := by decide
  have hdescent : baseEnd_1378104 < baseStart_1378104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378137 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_1378137 : Nat := 118140960795 + 1378137 * 2 ^ 59
def prefixEnd_1378137 : Nat := 4983230072969 + 3 ^ 40 * 1378137 * 2
def baseEnd_1378137 : Nat := 707646688745379766349569

theorem tailTrace_1378137 : CollatzResearch.WordTrace tailWord_1378137 prefixEnd_1378137 707646688745379766349569 := by
  unfold tailWord_1378137
  simp only [CollatzResearch.WordTrace]
  refine ⟨50264785808252490906180665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33509857205501660604120443 50264785808252490906180665)
  ·
    refine ⟨37698589356189368179635499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50264785808252490906180665 37698589356189368179635499)
    ·
      refine ⟨56547884034284052269453249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37698589356189368179635499 56547884034284052269453249)
      ·
        refine ⟨42410913025713039202089937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56547884034284052269453249 42410913025713039202089937)
        ·
          refine ⟨31808184769284779401567453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42410913025713039202089937 31808184769284779401567453)
          ·
            refine ⟨11928069288481792275587795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31808184769284779401567453 11928069288481792275587795)
            ·
              refine ⟨17892103932722688413381693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11928069288481792275587795 17892103932722688413381693)
              ·
                refine ⟨6709538974771008155018135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17892103932722688413381693 6709538974771008155018135)
                ·
                  refine ⟨10064308462156512232527203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6709538974771008155018135 10064308462156512232527203)
                  ·
                    refine ⟨15096462693234768348790805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10064308462156512232527203 15096462693234768348790805)
                    ·
                      refine ⟨707646688745379766349569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15096462693234768348790805 707646688745379766349569)
                      ·
                        rfl

theorem cell23_1378137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_1378137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378137 prefixEnd_1378137 := by exact prefixLift 1378137
  have htrace : WordTrace (prefixWord ++ tailWord_1378137) baseStart_1378137 baseEnd_1378137 := by
    simpa [prefixWord, tailWord_1378137, baseEnd_1378137] using wordTrace_append hprefix tailTrace_1378137
  have hstable : (prefixWord ++ tailWord_1378137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378137).length < 2 ^ (prefixWord ++ tailWord_1378137).sum := by decide
  have hdescent : baseEnd_1378137 < baseStart_1378137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378187 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 5]
def baseStart_1378187 : Nat := 118140960795 + 1378187 * 2 ^ 59
def prefixEnd_1378187 : Nat := 4983230072969 + 3 ^ 40 * 1378187 * 2
def baseEnd_1378187 : Nat := 707672362778104570724339

theorem tailTrace_1378187 : CollatzResearch.WordTrace tailWord_1378187 prefixEnd_1378187 707672362778104570724339 := by
  unfold tailWord_1378187
  simp only [CollatzResearch.WordTrace]
  refine ⟨50266609458071349445500815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33511072972047566297000543 50266609458071349445500815)
  ·
    refine ⟨75399914187107024168251223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50266609458071349445500815 75399914187107024168251223)
    ·
      refine ⟨113099871280660536252376835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75399914187107024168251223 113099871280660536252376835)
      ·
        refine ⟨169649806920990804378565253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113099871280660536252376835 169649806920990804378565253)
        ·
          refine ⟨31809338797685775820980985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169649806920990804378565253 31809338797685775820980985)
          ·
            refine ⟨23857004098264331865735739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31809338797685775820980985 23857004098264331865735739)
            ·
              refine ⟨35785506147396497798603609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23857004098264331865735739 35785506147396497798603609)
              ·
                refine ⟨26839129610547373348952707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35785506147396497798603609 26839129610547373348952707)
                ·
                  refine ⟨40258694415821060023429061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26839129610547373348952707 40258694415821060023429061)
                  ·
                    refine ⟨7548505202966448754392949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40258694415821060023429061 7548505202966448754392949)
                    ·
                      refine ⟨707672362778104570724339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7548505202966448754392949 707672362778104570724339)
                      ·
                        rfl

theorem cell23_1378187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_1378187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378187 prefixEnd_1378187 := by exact prefixLift 1378187
  have htrace : WordTrace (prefixWord ++ tailWord_1378187) baseStart_1378187 baseEnd_1378187 := by
    simpa [prefixWord, tailWord_1378187, baseEnd_1378187] using wordTrace_append hprefix tailTrace_1378187
  have hstable : (prefixWord ++ tailWord_1378187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378187).length < 2 ^ (prefixWord ++ tailWord_1378187).sum := by decide
  have hdescent : baseEnd_1378187 < baseStart_1378187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378201 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 3, 3, 2]
def baseStart_1378201 : Nat := 118140960795 + 1378201 * 2 ^ 59
def prefixEnd_1378201 : Nat := 4983230072969 + 3 ^ 40 * 1378201 * 2
def baseEnd_1378201 : Nat := 707679551507267515949275

theorem tailTrace_1378201 : CollatzResearch.WordTrace tailWord_1378201 prefixEnd_1378201 707679551507267515949275 := by
  unfold tailWord_1378201
  simp only [CollatzResearch.WordTrace]
  refine ⟨50267120080020629836510457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33511413386680419891006971 50267120080020629836510457)
  ·
    refine ⟨37700340060015472377382843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50267120080020629836510457 37700340060015472377382843)
    ·
      refine ⟨56550510090023208566074265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37700340060015472377382843 56550510090023208566074265)
      ·
        refine ⟨42412882567517406424555699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56550510090023208566074265 42412882567517406424555699)
        ·
          refine ⟨63619323851276109636833549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42412882567517406424555699 63619323851276109636833549)
          ·
            refine ⟨23857246444228541113812581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63619323851276109636833549 23857246444228541113812581)
            ·
              refine ⟨4473233708292851458839859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23857246444228541113812581 4473233708292851458839859)
              ·
                refine ⟨6709850562439277188259789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473233708292851458839859 6709850562439277188259789)
                ·
                  refine ⟨2516193960914728945597421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6709850562439277188259789 2516193960914728945597421)
                  ·
                    refine ⟨943572735343023354599033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2516193960914728945597421 943572735343023354599033)
                    ·
                      refine ⟨707679551507267515949275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943572735343023354599033 707679551507267515949275)
                      ·
                        rfl

theorem cell23_1378201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_1378201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378201 prefixEnd_1378201 := by exact prefixLift 1378201
  have htrace : WordTrace (prefixWord ++ tailWord_1378201) baseStart_1378201 baseEnd_1378201 := by
    simpa [prefixWord, tailWord_1378201, baseEnd_1378201] using wordTrace_append hprefix tailTrace_1378201
  have hstable : (prefixWord ++ tailWord_1378201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378201).length < 2 ^ (prefixWord ++ tailWord_1378201).sum := by decide
  have hdescent : baseEnd_1378201 < baseStart_1378201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378225 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1378225 : Nat := 118140960795 + 1378225 * 2 ^ 59
def prefixEnd_1378225 : Nat := 4983230072969 + 3 ^ 40 * 1378225 * 2
def baseEnd_1378225 : Nat := 707691875042975422049165

theorem tailTrace_1378225 : CollatzResearch.WordTrace tailWord_1378225 prefixEnd_1378225 707691875042975422049165 := by
  unfold tailWord_1378225
  simp only [CollatzResearch.WordTrace]
  refine ⟨50267995431933681935384129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33511996954622454623589419 50267995431933681935384129)
  ·
    refine ⟨37700996573950261451538097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50267995431933681935384129 37700996573950261451538097)
    ·
      refine ⟨28275747430462696088653573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37700996573950261451538097 28275747430462696088653573)
      ·
        refine ⟨5301702643211755516622545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28275747430462696088653573 5301702643211755516622545)
        ·
          refine ⟨3976276982408816637466909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5301702643211755516622545 3976276982408816637466909)
          ·
            refine ⟨1491103868403306239050091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3976276982408816637466909 1491103868403306239050091)
            ·
              refine ⟨2236655802604959358575137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491103868403306239050091 2236655802604959358575137)
              ·
                refine ⟨1677491851953719518931353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236655802604959358575137 1677491851953719518931353)
                ·
                  refine ⟨1258118888965289639198515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677491851953719518931353 1258118888965289639198515)
                  ·
                    refine ⟨1887178333447934458797773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1258118888965289639198515 1887178333447934458797773)
                    ·
                      refine ⟨707691875042975422049165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887178333447934458797773 707691875042975422049165)
                      ·
                        rfl

theorem cell23_1378225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1378225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378225 prefixEnd_1378225 := by exact prefixLift 1378225
  have htrace : WordTrace (prefixWord ++ tailWord_1378225) baseStart_1378225 baseEnd_1378225 := by
    simpa [prefixWord, tailWord_1378225, baseEnd_1378225] using wordTrace_append hprefix tailTrace_1378225
  have hstable : (prefixWord ++ tailWord_1378225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378225).length < 2 ^ (prefixWord ++ tailWord_1378225).sum := by decide
  have hdescent : baseEnd_1378225 < baseStart_1378225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378234 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_1378234 : Nat := 118140960795 + 1378234 * 2 ^ 59
def prefixEnd_1378234 : Nat := 4983230072969 + 3 ^ 40 * 1378234 * 2
def baseEnd_1378234 : Nat := 707696496368865886836623

theorem tailTrace_1378234 : CollatzResearch.WordTrace tailWord_1378234 prefixEnd_1378234 707696496368865886836623 := by
  unfold tailWord_1378234
  simp only [CollatzResearch.WordTrace]
  refine ⟨12567080922225269118115439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33512215792600717648307837 12567080922225269118115439)
  ·
    refine ⟨18850621383337903677173159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12567080922225269118115439 18850621383337903677173159)
    ·
      refine ⟨28275932075006855515759739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18850621383337903677173159 28275932075006855515759739)
      ·
        refine ⟨42413898112510283273639609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28275932075006855515759739 42413898112510283273639609)
        ·
          refine ⟨31810423584382712455229707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42413898112510283273639609 31810423584382712455229707)
          ·
            refine ⟨47715635376574068682844561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31810423584382712455229707 47715635376574068682844561)
            ·
              refine ⟨35786726532430551512133421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47715635376574068682844561 35786726532430551512133421)
              ·
                refine ⟨13420022449661456817050033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35786726532430551512133421 13420022449661456817050033)
                ·
                  refine ⟨10065016837246092612787525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13420022449661456817050033 10065016837246092612787525)
                  ·
                    refine ⟨1887190656983642364897661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10065016837246092612787525 1887190656983642364897661)
                    ·
                      refine ⟨707696496368865886836623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887190656983642364897661 707696496368865886836623)
                      ·
                        rfl

theorem cell23_1378234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_1378234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378234 prefixEnd_1378234 := by exact prefixLift 1378234
  have htrace : WordTrace (prefixWord ++ tailWord_1378234) baseStart_1378234 baseEnd_1378234 := by
    simpa [prefixWord, tailWord_1378234, baseEnd_1378234] using wordTrace_append hprefix tailTrace_1378234
  have hstable : (prefixWord ++ tailWord_1378234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378234).length < 2 ^ (prefixWord ++ tailWord_1378234).sum := by decide
  have hdescent : baseEnd_1378234 < baseStart_1378234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378248 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_1378248 : Nat := 118140960795 + 1378248 * 2 ^ 59
def prefixEnd_1378248 : Nat := 4983230072969 + 3 ^ 40 * 1378248 * 2
def baseEnd_1378248 : Nat := 707703685098028832061559

theorem tailTrace_1378248 : CollatzResearch.WordTrace tailWord_1378248 prefixEnd_1378248 707703685098028832061559 := by
  unfold tailWord_1378248
  simp only [CollatzResearch.WordTrace]
  refine ⟨25134417155425178431735699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33512556207233571242314265 25134417155425178431735699)
  ·
    refine ⟨37701625733137767647603549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25134417155425178431735699 37701625733137767647603549)
    ·
      refine ⟨14138109649926662867851331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37701625733137767647603549 14138109649926662867851331)
      ·
        refine ⟨21207164474889994301776997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14138109649926662867851331 21207164474889994301776997)
        ·
          refine ⟨3976343339041873931583187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21207164474889994301776997 3976343339041873931583187)
          ·
            refine ⟨5964515008562810897374781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3976343339041873931583187 5964515008562810897374781)
            ·
              refine ⟨2236693128211054086515543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5964515008562810897374781 2236693128211054086515543)
              ·
                refine ⟨3355039692316581129773315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236693128211054086515543 3355039692316581129773315)
                ·
                  refine ⟨5032559538474871694659973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355039692316581129773315 5032559538474871694659973)
                  ·
                    refine ⟨943604913464038442748745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5032559538474871694659973 943604913464038442748745)
                    ·
                      refine ⟨707703685098028832061559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943604913464038442748745 707703685098028832061559)
                      ·
                        rfl

theorem cell23_1378248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_1378248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378248 prefixEnd_1378248 := by exact prefixLift 1378248
  have htrace : WordTrace (prefixWord ++ tailWord_1378248) baseStart_1378248 baseEnd_1378248 := by
    simpa [prefixWord, tailWord_1378248, baseEnd_1378248] using wordTrace_append hprefix tailTrace_1378248
  have hstable : (prefixWord ++ tailWord_1378248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378248).length < 2 ^ (prefixWord ++ tailWord_1378248).sum := by decide
  have hdescent : baseEnd_1378248 < baseStart_1378248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378254 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_1378254 : Nat := 118140960795 + 1378254 * 2 ^ 59
def prefixEnd_1378254 : Nat := 4983230072969 + 3 ^ 40 * 1378254 * 2
def baseEnd_1378254 : Nat := 78634085109106200954059

theorem tailTrace_1378254 : CollatzResearch.WordTrace tailWord_1378254 prefixEnd_1378254 78634085109106200954059 := by
  unfold tailWord_1378254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6283631643603577486023727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33512702099219079925459877 6283631643603577486023727)
  ·
    refine ⟨9425447465405366229035591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6283631643603577486023727 9425447465405366229035591)
    ·
      refine ⟨14138171198108049343553387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9425447465405366229035591 14138171198108049343553387)
      ·
        refine ⟨21207256797162074015330081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14138171198108049343553387 21207256797162074015330081)
        ·
          refine ⟨15905442597871555511497561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21207256797162074015330081 15905442597871555511497561)
          ·
            refine ⟨11929081948403666633623171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15905442597871555511497561 11929081948403666633623171)
            ·
              refine ⟨17893622922605499950434757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11929081948403666633623171 17893622922605499950434757)
              ·
                refine ⟨3355054297988531240706517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17893622922605499950434757 3355054297988531240706517)
                ·
                  refine ⟨78634085109106200954059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3355054297988531240706517 78634085109106200954059)
                  ·
                    rfl

theorem cell23_1378254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_1378254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378254 prefixEnd_1378254 := by exact prefixLift 1378254
  have htrace : WordTrace (prefixWord ++ tailWord_1378254) baseStart_1378254 baseEnd_1378254 := by
    simpa [prefixWord, tailWord_1378254, baseEnd_1378254] using wordTrace_append hprefix tailTrace_1378254
  have hstable : (prefixWord ++ tailWord_1378254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378254).length < 2 ^ (prefixWord ++ tailWord_1378254).sum := by decide
  have hdescent : baseEnd_1378254 < baseStart_1378254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378304 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_1378304 : Nat := 118140960795 + 1378304 * 2 ^ 59
def prefixEnd_1378304 : Nat := 4983230072969 + 3 ^ 40 * 1378304 * 2
def baseEnd_1378304 : Nat := 707732440014680612961301

theorem tailTrace_1378304 : CollatzResearch.WordTrace tailWord_1378304 prefixEnd_1378304 707732440014680612961301 := by
  unfold tailWord_1378304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25135438399323739213754983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33513917865764985618339977 25135438399323739213754983)
  ·
    refine ⟨37703157598985608820632475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25135438399323739213754983 37703157598985608820632475)
    ·
      refine ⟨56554736398478413230948713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37703157598985608820632475 56554736398478413230948713)
      ·
        refine ⟨42416052298858809923211535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56554736398478413230948713 42416052298858809923211535)
        ·
          refine ⟨63624078448288214884817303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42416052298858809923211535 63624078448288214884817303)
          ·
            refine ⟨95436117672432322327225955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63624078448288214884817303 95436117672432322327225955)
            ·
              refine ⟨143154176508648483490838933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95436117672432322327225955 143154176508648483490838933)
              ·
                refine ⟨6710352023842897663633075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143154176508648483490838933 6710352023842897663633075)
                ·
                  refine ⟨10065528035764346495449613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6710352023842897663633075 10065528035764346495449613)
                  ·
                    refine ⟨3774573013411629935793605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10065528035764346495449613 3774573013411629935793605)
                    ·
                      refine ⟨707732440014680612961301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3774573013411629935793605 707732440014680612961301)
                      ·
                        rfl

theorem cell23_1378304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_1378304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378304 prefixEnd_1378304 := by exact prefixLift 1378304
  have htrace : WordTrace (prefixWord ++ tailWord_1378304) baseStart_1378304 baseEnd_1378304 := by
    simpa [prefixWord, tailWord_1378304, baseEnd_1378304] using wordTrace_append hprefix tailTrace_1378304
  have hstable : (prefixWord ++ tailWord_1378304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378304).length < 2 ^ (prefixWord ++ tailWord_1378304).sum := by decide
  have hdescent : baseEnd_1378304 < baseStart_1378304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378321 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 6, 4, 2]
def baseStart_1378321 : Nat := 118140960795 + 1378321 * 2 ^ 59
def prefixEnd_1378321 : Nat := 4983230072969 + 3 ^ 40 * 1378321 * 2
def baseEnd_1378321 : Nat := 707741169185807046448723

theorem tailTrace_1378321 : CollatzResearch.WordTrace tailWord_1378321 prefixEnd_1378321 707741169185807046448723 := by
  unfold tailWord_1378321
  simp only [CollatzResearch.WordTrace]
  refine ⟨50271496839585890330878817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33514331226390593553919211 50271496839585890330878817)
  ·
    refine ⟨37703622629689417748159113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50271496839585890330878817 37703622629689417748159113)
    ·
      refine ⟨28277716972267063311119335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37703622629689417748159113 28277716972267063311119335)
      ·
        refine ⟨42416575458400594966679003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28277716972267063311119335 42416575458400594966679003)
        ·
          refine ⟨63624863187600892450018505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42416575458400594966679003 63624863187600892450018505)
          ·
            refine ⟨47718647390700669337513879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63624863187600892450018505 47718647390700669337513879)
            ·
              refine ⟨71577971086051004006270819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47718647390700669337513879 71577971086051004006270819)
              ·
                refine ⟨107366956629076506009406229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71577971086051004006270819 107366956629076506009406229)
                ·
                  refine ⟨5032826091987961219190917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107366956629076506009406229 5032826091987961219190917)
                  ·
                    refine ⟨943654892247742728598297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5032826091987961219190917 943654892247742728598297)
                    ·
                      refine ⟨707741169185807046448723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943654892247742728598297 707741169185807046448723)
                      ·
                        rfl

theorem cell23_1378321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_1378321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378321 prefixEnd_1378321 := by exact prefixLift 1378321
  have htrace : WordTrace (prefixWord ++ tailWord_1378321) baseStart_1378321 baseEnd_1378321 := by
    simpa [prefixWord, tailWord_1378321, baseEnd_1378321] using wordTrace_append hprefix tailTrace_1378321
  have hstable : (prefixWord ++ tailWord_1378321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378321).length < 2 ^ (prefixWord ++ tailWord_1378321).sum := by decide
  have hdescent : baseEnd_1378321 < baseStart_1378321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378338 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_1378338 : Nat := 118140960795 + 1378338 * 2 ^ 59
def prefixEnd_1378338 : Nat := 4983230072969 + 3 ^ 40 * 1378338 * 2
def baseEnd_1378338 : Nat := 707749898356933479936145

theorem tailTrace_1378338 : CollatzResearch.WordTrace tailWord_1378338 prefixEnd_1378338 707749898356933479936145 := by
  unfold tailWord_1378338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568029220131075558561917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33514744587016201489498445 12568029220131075558561917)
  ·
    refine ⟨4713010957549153334460719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12568029220131075558561917 4713010957549153334460719)
    ·
      refine ⟨7069516436323730001691079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4713010957549153334460719 7069516436323730001691079)
      ·
        refine ⟨10604274654485595002536619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7069516436323730001691079 10604274654485595002536619)
        ·
          refine ⟨15906411981728392503804929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10604274654485595002536619 15906411981728392503804929)
          ·
            refine ⟨11929808986296294377853697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15906411981728392503804929 11929808986296294377853697)
            ·
              refine ⟨8947356739722220783390273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11929808986296294377853697 8947356739722220783390273)
              ·
                refine ⟨6710517554791665587542705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8947356739722220783390273 6710517554791665587542705)
                ·
                  refine ⟨5032888166093749190657029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6710517554791665587542705 5032888166093749190657029)
                  ·
                    refine ⟨943666531142577973248193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5032888166093749190657029 943666531142577973248193)
                    ·
                      refine ⟨707749898356933479936145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943666531142577973248193 707749898356933479936145)
                      ·
                        rfl

theorem cell23_1378338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_1378338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378338 prefixEnd_1378338 := by exact prefixLift 1378338
  have htrace : WordTrace (prefixWord ++ tailWord_1378338) baseStart_1378338 baseEnd_1378338 := by
    simpa [prefixWord, tailWord_1378338, baseEnd_1378338] using wordTrace_append hprefix tailTrace_1378338
  have hstable : (prefixWord ++ tailWord_1378338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378338).length < 2 ^ (prefixWord ++ tailWord_1378338).sum := by decide
  have hdescent : baseEnd_1378338 < baseStart_1378338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378358 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1378358 : Nat := 118140960795 + 1378358 * 2 ^ 59
def prefixEnd_1378358 : Nat := 4983230072969 + 3 ^ 40 * 1378358 * 2
def baseEnd_1378358 : Nat := 707760167970023401686053

theorem tailTrace_1378358 : CollatzResearch.WordTrace tailWord_1378358 prefixEnd_1378358 707760167970023401686053 := by
  unfold tailWord_1378358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142052896278240353123483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33515230893634563766650485 3142052896278240353123483)
  ·
    refine ⟨4713079344417360529685225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3142052896278240353123483 4713079344417360529685225)
    ·
      refine ⟨3534809508313020397263919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4713079344417360529685225 3534809508313020397263919)
      ·
        refine ⟨5302214262469530595895879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534809508313020397263919 5302214262469530595895879)
        ·
          refine ⟨7953321393704295893843819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5302214262469530595895879 7953321393704295893843819)
          ·
            refine ⟨11929982090556443840765729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7953321393704295893843819 11929982090556443840765729)
            ·
              refine ⟨8947486567917332880574297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11929982090556443840765729 8947486567917332880574297)
              ·
                refine ⟨6710614925937999660430723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8947486567917332880574297 6710614925937999660430723)
                ·
                  refine ⟨10065922388906999490646085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6710614925937999660430723 10065922388906999490646085)
                  ·
                    refine ⟨1887360447920062404496141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10065922388906999490646085 1887360447920062404496141)
                    ·
                      refine ⟨707760167970023401686053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887360447920062404496141 707760167970023401686053)
                      ·
                        rfl

theorem cell23_1378358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1378358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378358 prefixEnd_1378358 := by exact prefixLift 1378358
  have htrace : WordTrace (prefixWord ++ tailWord_1378358) baseStart_1378358 baseEnd_1378358 := by
    simpa [prefixWord, tailWord_1378358, baseEnd_1378358] using wordTrace_append hprefix tailTrace_1378358
  have hstable : (prefixWord ++ tailWord_1378358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378358).length < 2 ^ (prefixWord ++ tailWord_1378358).sum := by decide
  have hdescent : baseEnd_1378358 < baseStart_1378358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378384 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_1378384 : Nat := 118140960795 + 1378384 * 2 ^ 59
def prefixEnd_1378384 : Nat := 4983230072969 + 3 ^ 40 * 1378384 * 2
def baseEnd_1378384 : Nat := 707773518467040299960933

theorem tailTrace_1378384 : CollatzResearch.WordTrace tailWord_1378384 prefixEnd_1378384 707773518467040299960933 := by
  unfold tailWord_1378384
  simp only [CollatzResearch.WordTrace]
  refine ⟨25136897319178826045211103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33515863092238434726948137 25136897319178826045211103)
  ·
    refine ⟨37705345978768239067816655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25136897319178826045211103 37705345978768239067816655)
    ·
      refine ⟨56558018968152358601724983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37705345978768239067816655 56558018968152358601724983)
      ·
        refine ⟨84837028452228537902587475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56558018968152358601724983 84837028452228537902587475)
        ·
          refine ⟨127255542678342806853881213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84837028452228537902587475 127255542678342806853881213)
          ·
            refine ⟨47720828504378552570205455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127255542678342806853881213 47720828504378552570205455)
            ·
              refine ⟨71581242756567828855308183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47720828504378552570205455 71581242756567828855308183)
              ·
                refine ⟨107371864134851743282962275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71581242756567828855308183 107371864134851743282962275)
                ·
                  refine ⟨161057796202277614924443413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107371864134851743282962275 161057796202277614924443413)
                  ·
                    refine ⟨7549584196981763199583285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161057796202277614924443413 7549584196981763199583285)
                    ·
                      refine ⟨707773518467040299960933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7549584196981763199583285 707773518467040299960933)
                      ·
                        rfl

theorem cell23_1378384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_1378384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378384 prefixEnd_1378384 := by exact prefixLift 1378384
  have htrace : WordTrace (prefixWord ++ tailWord_1378384) baseStart_1378384 baseEnd_1378384 := by
    simpa [prefixWord, tailWord_1378384, baseEnd_1378384] using wordTrace_append hprefix tailTrace_1378384
  have hstable : (prefixWord ++ tailWord_1378384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378384).length < 2 ^ (prefixWord ++ tailWord_1378384).sum := by decide
  have hdescent : baseEnd_1378384 < baseStart_1378384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378388 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_1378388 : Nat := 118140960795 + 1378388 * 2 ^ 59
def prefixEnd_1378388 : Nat := 4983230072969 + 3 ^ 40 * 1378388 * 2
def baseEnd_1378388 : Nat := 707775572389658284310915

theorem tailTrace_1378388 : CollatzResearch.WordTrace tailWord_1378388 prefixEnd_1378388 707775572389658284310915 := by
  unfold tailWord_1378388
  simp only [CollatzResearch.WordTrace]
  refine ⟨25136970265171580386783909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33515960353562107182378545 25136970265171580386783909)
  ·
    refine ⟨4713181924719671322521983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25136970265171580386783909 4713181924719671322521983)
    ·
      refine ⟨7069772887079506983782975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4713181924719671322521983 7069772887079506983782975)
      ·
        refine ⟨10604659330619260475674463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7069772887079506983782975 10604659330619260475674463)
        ·
          refine ⟨15906988995928890713511695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10604659330619260475674463 15906988995928890713511695)
          ·
            refine ⟨23860483493893336070267543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15906988995928890713511695 23860483493893336070267543)
            ·
              refine ⟨35790725240840004105401315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23860483493893336070267543 35790725240840004105401315)
              ·
                refine ⟨53686087861260006158101973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35790725240840004105401315 53686087861260006158101973)
                ·
                  refine ⟨1258267684248281394330515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 53686087861260006158101973 1258267684248281394330515)
                  ·
                    refine ⟨1887401526372422091495773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1258267684248281394330515 1887401526372422091495773)
                    ·
                      refine ⟨707775572389658284310915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887401526372422091495773 707775572389658284310915)
                      ·
                        rfl

theorem cell23_1378388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_1378388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378388 prefixEnd_1378388 := by exact prefixLift 1378388
  have htrace : WordTrace (prefixWord ++ tailWord_1378388) baseStart_1378388 baseEnd_1378388 := by
    simpa [prefixWord, tailWord_1378388, baseEnd_1378388] using wordTrace_append hprefix tailTrace_1378388
  have hstable : (prefixWord ++ tailWord_1378388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378388).length < 2 ^ (prefixWord ++ tailWord_1378388).sum := by decide
  have hdescent : baseEnd_1378388 < baseStart_1378388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378405 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_1378405 : Nat := 118140960795 + 1378405 * 2 ^ 59
def prefixEnd_1378405 : Nat := 4983230072969 + 3 ^ 40 * 1378405 * 2
def baseEnd_1378405 : Nat := 707784301560784717798337

theorem tailTrace_1378405 : CollatzResearch.WordTrace tailWord_1378405 prefixEnd_1378405 707784301560784717798337 := by
  unfold tailWord_1378405
  simp only [CollatzResearch.WordTrace]
  refine ⟨50274560571281572676936669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33516373714187715117957779 50274560571281572676936669)
  ·
    refine ⟨18852960214230589753851251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50274560571281572676936669 18852960214230589753851251)
    ·
      refine ⟨28279440321345884630776877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18852960214230589753851251 28279440321345884630776877)
      ·
        refine ⟨10604790120504706736541329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28279440321345884630776877 10604790120504706736541329)
        ·
          refine ⟨7953592590378530052405997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10604790120504706736541329 7953592590378530052405997)
          ·
            refine ⟨2982597221391948769652249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7953592590378530052405997 2982597221391948769652249)
            ·
              refine ⟨2236947916043961577239187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2982597221391948769652249 2236947916043961577239187)
              ·
                refine ⟨3355421874065942365858781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236947916043961577239187 3355421874065942365858781)
                ·
                  refine ⟨1258283202774728387197043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3355421874065942365858781 1258283202774728387197043)
                  ·
                    refine ⟨1887424804162092580795565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1258283202774728387197043 1887424804162092580795565)
                    ·
                      refine ⟨707784301560784717798337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887424804162092580795565 707784301560784717798337)
                      ·
                        rfl

theorem cell23_1378405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_1378405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378405 prefixEnd_1378405 := by exact prefixLift 1378405
  have htrace : WordTrace (prefixWord ++ tailWord_1378405) baseStart_1378405 baseEnd_1378405 := by
    simpa [prefixWord, tailWord_1378405, baseEnd_1378405] using wordTrace_append hprefix tailTrace_1378405
  have hstable : (prefixWord ++ tailWord_1378405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378405).length < 2 ^ (prefixWord ++ tailWord_1378405).sum := by decide
  have hdescent : baseEnd_1378405 < baseStart_1378405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378428 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_1378428 : Nat := 118140960795 + 1378428 * 2 ^ 59
def prefixEnd_1378428 : Nat := 4983230072969 + 3 ^ 40 * 1378428 * 2
def baseEnd_1378428 : Nat := 707796111615838127810731

theorem tailTrace_1378428 : CollatzResearch.WordTrace tailWord_1378428 prefixEnd_1378428 707796111615838127810731 := by
  unfold tailWord_1378428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25137699725099123802511969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33516932966798831736682625 25137699725099123802511969)
  ·
    refine ⟨18853274793824342851883977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25137699725099123802511969 18853274793824342851883977)
    ·
      refine ⟨14139956095368257138912983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18853274793824342851883977 14139956095368257138912983)
      ·
        refine ⟨21209934143052385708369475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14139956095368257138912983 21209934143052385708369475)
        ·
          refine ⟨31814901214578578562554213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21209934143052385708369475 31814901214578578562554213)
          ·
            refine ⟨5965293977733483480478915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31814901214578578562554213 5965293977733483480478915)
            ·
              refine ⟨8947940966600225220718373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5965293977733483480478915 8947940966600225220718373)
              ·
                refine ⟨1677738931237542228884695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8947940966600225220718373 1677738931237542228884695)
                ·
                  refine ⟨2516608396856313343327043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677738931237542228884695 2516608396856313343327043)
                  ·
                    refine ⟨3774912595284470014990565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2516608396856313343327043 3774912595284470014990565)
                    ·
                      refine ⟨707796111615838127810731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3774912595284470014990565 707796111615838127810731)
                      ·
                        rfl

theorem cell23_1378428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_1378428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378428 prefixEnd_1378428 := by exact prefixLift 1378428
  have htrace : WordTrace (prefixWord ++ tailWord_1378428) baseStart_1378428 baseEnd_1378428 := by
    simpa [prefixWord, tailWord_1378428, baseEnd_1378428] using wordTrace_append hprefix tailTrace_1378428
  have hstable : (prefixWord ++ tailWord_1378428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378428).length < 2 ^ (prefixWord ++ tailWord_1378428).sum := by decide
  have hdescent : baseEnd_1378428 < baseStart_1378428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378441 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_1378441 : Nat := 118140960795 + 1378441 * 2 ^ 59
def prefixEnd_1378441 : Nat := 4983230072969 + 3 ^ 40 * 1378441 * 2
def baseEnd_1378441 : Nat := 707802786864346576948171

theorem tailTrace_1378441 : CollatzResearch.WordTrace tailWord_1378441 prefixEnd_1378441 707802786864346576948171 := by
  unfold tailWord_1378441
  simp only [CollatzResearch.WordTrace]
  refine ⟨50275873599151150825247177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33517249066100767216831451 50275873599151150825247177)
  ·
    refine ⟨37706905199363363118935383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50275873599151150825247177 37706905199363363118935383)
    ·
      refine ⟨56560357799045044678403075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37706905199363363118935383 56560357799045044678403075)
      ·
        refine ⟨84840536698567567017604613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56560357799045044678403075 84840536698567567017604613)
        ·
          refine ⟨15907600630981418815800865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84840536698567567017604613 15907600630981418815800865)
          ·
            refine ⟨11930700473236064111850649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15907600630981418815800865 11930700473236064111850649)
            ·
              refine ⟨8948025354927048083887987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11930700473236064111850649 8948025354927048083887987)
              ·
                refine ⟨13422038032390572125831981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8948025354927048083887987 13422038032390572125831981)
                ·
                  refine ⟨5033264262146464547186993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13422038032390572125831981 5033264262146464547186993)
                  ·
                    refine ⟨3774948196609848410390245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5033264262146464547186993 3774948196609848410390245)
                    ·
                      refine ⟨707802786864346576948171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3774948196609848410390245 707802786864346576948171)
                      ·
                        rfl

theorem cell23_1378441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_1378441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378441 prefixEnd_1378441 := by exact prefixLift 1378441
  have htrace : WordTrace (prefixWord ++ tailWord_1378441) baseStart_1378441 baseEnd_1378441 := by
    simpa [prefixWord, tailWord_1378441, baseEnd_1378441] using wordTrace_append hprefix tailTrace_1378441
  have hstable : (prefixWord ++ tailWord_1378441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378441).length < 2 ^ (prefixWord ++ tailWord_1378441).sum := by decide
  have hdescent : baseEnd_1378441 < baseStart_1378441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378448 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 3]
def baseStart_1378448 : Nat := 118140960795 + 1378448 * 2 ^ 59
def prefixEnd_1378448 : Nat := 4983230072969 + 3 ^ 40 * 1378448 * 2
def baseEnd_1378448 : Nat := 707806381228928049560639

theorem tailTrace_1378448 : CollatzResearch.WordTrace tailWord_1378448 prefixEnd_1378448 707806381228928049560639 := by
  unfold tailWord_1378448
  simp only [CollatzResearch.WordTrace]
  refine ⟨25138064455062895510375999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33517419273417194013834665 25138064455062895510375999)
  ·
    refine ⟨37707096682594343265563999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25138064455062895510375999 37707096682594343265563999)
    ·
      refine ⟨56560645023891514898345999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37707096682594343265563999 56560645023891514898345999)
      ·
        refine ⟨84840967535837272347518999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56560645023891514898345999 84840967535837272347518999)
        ·
          refine ⟨127261451303755908521278499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84840967535837272347518999 127261451303755908521278499)
          ·
            refine ⟨190892176955633862781917749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127261451303755908521278499 190892176955633862781917749)
            ·
              refine ⟨17896141589590674635804789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190892176955633862781917749 17896141589590674635804789)
              ·
                refine ⟨1677763274024125747106699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17896141589590674635804789 1677763274024125747106699)
                ·
                  refine ⟨2516644911036188620660049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677763274024125747106699 2516644911036188620660049)
                  ·
                    refine ⟨1887483683277141465495037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2516644911036188620660049 1887483683277141465495037)
                    ·
                      refine ⟨707806381228928049560639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887483683277141465495037 707806381228928049560639)
                      ·
                        rfl

theorem cell23_1378448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 3].length) (baseStart_1378448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378448 prefixEnd_1378448 := by exact prefixLift 1378448
  have htrace : WordTrace (prefixWord ++ tailWord_1378448) baseStart_1378448 baseEnd_1378448 := by
    simpa [prefixWord, tailWord_1378448, baseEnd_1378448] using wordTrace_append hprefix tailTrace_1378448
  have hstable : (prefixWord ++ tailWord_1378448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378448).length < 2 ^ (prefixWord ++ tailWord_1378448).sum := by decide
  have hdescent : baseEnd_1378448 < baseStart_1378448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378468 : List Nat := [2, 3, 1, 2, 4, 1, 2, 8]
def baseStart_1378468 : Nat := 118140960795 + 1378468 * 2 ^ 59
def prefixEnd_1378468 : Nat := 4983230072969 + 3 ^ 40 * 1378468 * 2
def baseEnd_1378468 : Nat := 26215431512667332270761

theorem tailTrace_1378468 : CollatzResearch.WordTrace tailWord_1378468 prefixEnd_1378468 26215431512667332270761 := by
  unfold tailWord_1378468
  simp only [CollatzResearch.WordTrace]
  refine ⟨25138429185026667218240029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33517905580035556290986705 25138429185026667218240029)
  ·
    refine ⟨9426910944385000206840011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25138429185026667218240029 9426910944385000206840011)
    ·
      refine ⟨14140366416577500310260017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9426910944385000206840011 14140366416577500310260017)
      ·
        refine ⟨10605274812433125232695013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14140366416577500310260017 10605274812433125232695013)
        ·
          refine ⟨1988489027331210981130315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10605274812433125232695013 1988489027331210981130315)
          ·
            refine ⟨2982733540996816471695473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988489027331210981130315 2982733540996816471695473)
            ·
              refine ⟨2237050155747612353771605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2982733540996816471695473 2237050155747612353771605)
              ·
                refine ⟨26215431512667332270761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2237050155747612353771605 26215431512667332270761)
                ·
                  rfl

theorem cell23_1378468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 8].length) (baseStart_1378468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378468 prefixEnd_1378468 := by exact prefixLift 1378468
  have htrace : WordTrace (prefixWord ++ tailWord_1378468) baseStart_1378468 baseEnd_1378468 := by
    simpa [prefixWord, tailWord_1378468, baseEnd_1378468] using wordTrace_append hprefix tailTrace_1378468
  have hstable : (prefixWord ++ tailWord_1378468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378468).length < 2 ^ (prefixWord ++ tailWord_1378468).sum := by decide
  have hdescent : baseEnd_1378468 < baseStart_1378468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378511 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 2, 6]
def baseStart_1378511 : Nat := 118140960795 + 1378511 * 2 ^ 59
def prefixEnd_1378511 : Nat := 4983230072969 + 3 ^ 40 * 1378511 * 2
def baseEnd_1378511 : Nat := 235946243503387101024283

theorem tailTrace_1378511 : CollatzResearch.WordTrace tailWord_1378511 prefixEnd_1378511 235946243503387101024283 := by
  unfold tailWord_1378511
  simp only [CollatzResearch.WordTrace]
  refine ⟨50278426708897552780295387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33518951139265035186863591 50278426708897552780295387)
  ·
    refine ⟨75417640063346329170443081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50278426708897552780295387 75417640063346329170443081)
    ·
      refine ⟨56563230047509746877832311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75417640063346329170443081 56563230047509746877832311)
      ·
        refine ⟨84844845071264620316748467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56563230047509746877832311 84844845071264620316748467)
        ·
          refine ⟨127267267606896930475122701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84844845071264620316748467 127267267606896930475122701)
          ·
            refine ⟨47725225352586348928171013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127267267606896930475122701 47725225352586348928171013)
            ·
              refine ⟨8948479753609940424032065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47725225352586348928171013 8948479753609940424032065)
              ·
                refine ⟨6711359815207455318024049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8948479753609940424032065 6711359815207455318024049)
                ·
                  refine ⟨5033519861405591488518037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6711359815207455318024049 5033519861405591488518037)
                  ·
                    refine ⟨235946243503387101024283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5033519861405591488518037 235946243503387101024283)
                    ·
                      rfl

theorem cell23_1378511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_1378511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378511 prefixEnd_1378511 := by exact prefixLift 1378511
  have htrace : WordTrace (prefixWord ++ tailWord_1378511) baseStart_1378511 baseEnd_1378511 := by
    simpa [prefixWord, tailWord_1378511, baseEnd_1378511] using wordTrace_append hprefix tailTrace_1378511
  have hstable : (prefixWord ++ tailWord_1378511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378511).length < 2 ^ (prefixWord ++ tailWord_1378511).sum := by decide
  have hdescent : baseEnd_1378511 < baseStart_1378511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378521 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_1378521 : Nat := 118140960795 + 1378521 * 2 ^ 59
def prefixEnd_1378521 : Nat := 4983230072969 + 3 ^ 40 * 1378521 * 2
def baseEnd_1378521 : Nat := 707843865316706263947803

theorem tailTrace_1378521 : CollatzResearch.WordTrace tailWord_1378521 prefixEnd_1378521 707843865316706263947803 := by
  unfold tailWord_1378521
  simp only [CollatzResearch.WordTrace]
  refine ⟨50278791438861324488159417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33519194292574216325439611 50278791438861324488159417)
  ·
    refine ⟨37709093579145993366119563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50278791438861324488159417 37709093579145993366119563)
    ·
      refine ⟨56563640368718990049179345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37709093579145993366119563 56563640368718990049179345)
      ·
        refine ⟨42422730276539242536884509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56563640368718990049179345 42422730276539242536884509)
        ·
          refine ⟨15908523853702215951331691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42422730276539242536884509 15908523853702215951331691)
          ·
            refine ⟨23862785780553323926997537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15908523853702215951331691 23862785780553323926997537)
            ·
              refine ⟨17897089335414992945248153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23862785780553323926997537 17897089335414992945248153)
              ·
                refine ⟨13422817001561244708936115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17897089335414992945248153 13422817001561244708936115)
                ·
                  refine ⟨20134225502341867063404173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13422817001561244708936115 20134225502341867063404173)
                  ·
                    refine ⟨7550334563378200148776565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20134225502341867063404173 7550334563378200148776565)
                    ·
                      refine ⟨707843865316706263947803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7550334563378200148776565 707843865316706263947803)
                      ·
                        rfl

theorem cell23_1378521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_1378521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378521 prefixEnd_1378521 := by exact prefixLift 1378521
  have htrace : WordTrace (prefixWord ++ tailWord_1378521) baseStart_1378521 baseEnd_1378521 := by
    simpa [prefixWord, tailWord_1378521, baseEnd_1378521] using wordTrace_append hprefix tailTrace_1378521
  have hstable : (prefixWord ++ tailWord_1378521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378521).length < 2 ^ (prefixWord ++ tailWord_1378521).sum := by decide
  have hdescent : baseEnd_1378521 < baseStart_1378521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
