import V185TrunkScan23Chunk0389

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2304824 : List Nat := [2, 1, 2, 1, 3, 2, 1, 11]
def baseStart_2304824 : Nat := 118140960795 + 2304824 * 2 ^ 59
def prefixEnd_2304824 : Nat := 4983230072969 + 3 ^ 40 * 2304824 * 2
def baseEnd_2304824 : Nat := 43832686519199837007419

theorem tailTrace_2304824 : CollatzResearch.WordTrace tailWord_2304824 prefixEnd_2304824 43832686519199837007419 := by
  unfold tailWord_2304824
  simp only [CollatzResearch.WordTrace]
  refine ⟨42031918701011877722808763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56042558268015836963745017 42031918701011877722808763)
  ·
    refine ⟨63047878051517816584213145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42031918701011877722808763 63047878051517816584213145)
    ·
      refine ⟨47285908538638362438159859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63047878051517816584213145 47285908538638362438159859)
      ·
        refine ⟨70928862807957543657239789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47285908538638362438159859 70928862807957543657239789)
        ·
          refine ⟨26598323552984078871464921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70928862807957543657239789 26598323552984078871464921)
          ·
            refine ⟨19948742664738059153598691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26598323552984078871464921 19948742664738059153598691)
            ·
              refine ⟨29923113997107088730398037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19948742664738059153598691 29923113997107088730398037)
              ·
                refine ⟨43832686519199837007419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 29923113997107088730398037 43832686519199837007419)
                ·
                  rfl

theorem cell23_2304824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 11].length) (baseStart_2304824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304824 prefixEnd_2304824 := by exact prefixLift 2304824
  have htrace : WordTrace (prefixWord ++ tailWord_2304824) baseStart_2304824 baseEnd_2304824 := by
    simpa [prefixWord, tailWord_2304824, baseEnd_2304824] using wordTrace_append hprefix tailTrace_2304824
  have hstable : (prefixWord ++ tailWord_2304824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304824).length < 2 ^ (prefixWord ++ tailWord_2304824).sum := by decide
  have hdescent : baseEnd_2304824 < baseStart_2304824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304831 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_2304831 : Nat := 118140960795 + 2304831 * 2 ^ 59
def prefixEnd_2304831 : Nat := 4983230072969 + 3 ^ 40 * 2304831 * 2
def baseEnd_2304831 : Nat := 1183486130382977071812781

theorem tailTrace_2304831 : CollatzResearch.WordTrace tailWord_2304831 prefixEnd_2304831 1183486130382977071812781 := by
  unfold tailWord_2304831
  simp only [CollatzResearch.WordTrace]
  refine ⟨84064092712998395641122347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56042728475332263760748231 84064092712998395641122347)
  ·
    refine ⟨126096139069497593461683521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84064092712998395641122347 126096139069497593461683521)
    ·
      refine ⟨94572104302123195096262641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126096139069497593461683521 94572104302123195096262641)
      ·
        refine ⟨70929078226592396322196981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94572104302123195096262641 70929078226592396322196981)
        ·
          refine ⟨6649601083743037155205967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70929078226592396322196981 6649601083743037155205967)
          ·
            refine ⟨9974401625614555732808951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6649601083743037155205967 9974401625614555732808951)
            ·
              refine ⟨14961602438421833599213427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9974401625614555732808951 14961602438421833599213427)
              ·
                refine ⟨22442403657632750398820141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14961602438421833599213427 22442403657632750398820141)
                ·
                  refine ⟨8415901371612281399557553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22442403657632750398820141 8415901371612281399557553)
                  ·
                    refine ⟨6311926028709211049668165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8415901371612281399557553 6311926028709211049668165)
                    ·
                      refine ⟨1183486130382977071812781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6311926028709211049668165 1183486130382977071812781)
                      ·
                        rfl

theorem cell23_2304831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_2304831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304831 prefixEnd_2304831 := by exact prefixLift 2304831
  have htrace : WordTrace (prefixWord ++ tailWord_2304831) baseStart_2304831 baseEnd_2304831 := by
    simpa [prefixWord, tailWord_2304831, baseEnd_2304831] using wordTrace_append hprefix tailTrace_2304831
  have hstable : (prefixWord ++ tailWord_2304831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304831).length < 2 ^ (prefixWord ++ tailWord_2304831).sum := by decide
  have hdescent : baseEnd_2304831 < baseStart_2304831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304868 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_2304868 : Nat := 118140960795 + 2304868 * 2 ^ 59
def prefixEnd_2304868 : Nat := 4983230072969 + 3 ^ 40 * 2304868 * 2
def baseEnd_2304868 : Nat := 1183505129167193427050111

theorem tailTrace_2304868 : CollatzResearch.WordTrace tailWord_2304868 prefixEnd_2304868 1183505129167193427050111 := by
  unfold tailWord_2304868
  simp only [CollatzResearch.WordTrace]
  refine ⟨42032721106932175480109629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56043628142576233973479505 42032721106932175480109629)
  ·
    refine ⟨15762270415099565805041111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42032721106932175480109629 15762270415099565805041111)
    ·
      refine ⟨23643405622649348707561667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15762270415099565805041111 23643405622649348707561667)
      ·
        refine ⟨35465108433974023061342501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23643405622649348707561667 35465108433974023061342501)
        ·
          refine ⟨6649707831370129324001719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35465108433974023061342501 6649707831370129324001719)
          ·
            refine ⟨9974561747055193986002579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6649707831370129324001719 9974561747055193986002579)
            ·
              refine ⟨14961842620582790979003869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9974561747055193986002579 14961842620582790979003869)
              ·
                refine ⟨5610690982718546617126451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14961842620582790979003869 5610690982718546617126451)
                ·
                  refine ⟨8416036474077819925689677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5610690982718546617126451 8416036474077819925689677)
                  ·
                    refine ⟨3156013677779182472133629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8416036474077819925689677 3156013677779182472133629)
                    ·
                      refine ⟨1183505129167193427050111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3156013677779182472133629 1183505129167193427050111)
                      ·
                        rfl

theorem cell23_2304868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_2304868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304868 prefixEnd_2304868 := by exact prefixLift 2304868
  have htrace : WordTrace (prefixWord ++ tailWord_2304868) baseStart_2304868 baseEnd_2304868 := by
    simpa [prefixWord, tailWord_2304868, baseEnd_2304868] using wordTrace_append hprefix tailTrace_2304868
  have hstable : (prefixWord ++ tailWord_2304868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304868).length < 2 ^ (prefixWord ++ tailWord_2304868).sum := by decide
  have hdescent : baseEnd_2304868 < baseStart_2304868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304886 : List Nat := [5, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2304886 : Nat := 118140960795 + 2304886 * 2 ^ 59
def prefixEnd_2304886 : Nat := 4983230072969 + 3 ^ 40 * 2304886 * 2
def baseEnd_2304886 : Nat := 1183514371818974356625029

theorem tailTrace_2304886 : CollatzResearch.WordTrace tailWord_2304886 prefixEnd_2304886 1183514371818974356625029 := by
  unfold tailWord_2304886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254131170487446252148407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56044065818532760022916341 5254131170487446252148407)
  ·
    refine ⟨7881196755731169378222611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5254131170487446252148407 7881196755731169378222611)
    ·
      refine ⟨11821795133596754067333917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7881196755731169378222611 11821795133596754067333917)
      ·
        refine ⟨4433173175098782775250219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11821795133596754067333917 4433173175098782775250219)
        ·
          refine ⟨6649759762648174162875329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4433173175098782775250219 6649759762648174162875329)
          ·
            refine ⟨4987319821986130622156497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6649759762648174162875329 4987319821986130622156497)
            ·
              refine ⟨3740489866489597966617373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4987319821986130622156497 3740489866489597966617373)
              ·
                refine ⟨1402683699933599237481515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3740489866489597966617373 1402683699933599237481515)
                ·
                  refine ⟨2104025549900398856222273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402683699933599237481515 2104025549900398856222273)
                  ·
                    refine ⟨1578019162425299142166705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2104025549900398856222273 1578019162425299142166705)
                    ·
                      refine ⟨1183514371818974356625029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578019162425299142166705 1183514371818974356625029)
                      ·
                        rfl

theorem cell23_2304886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2304886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304886 prefixEnd_2304886 := by exact prefixLift 2304886
  have htrace : WordTrace (prefixWord ++ tailWord_2304886) baseStart_2304886 baseEnd_2304886 := by
    simpa [prefixWord, tailWord_2304886, baseEnd_2304886] using wordTrace_append hprefix tailTrace_2304886
  have hstable : (prefixWord ++ tailWord_2304886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304886).length < 2 ^ (prefixWord ++ tailWord_2304886).sum := by decide
  have hdescent : baseEnd_2304886 < baseStart_2304886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304901 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_2304901 : Nat := 118140960795 + 2304901 * 2 ^ 59
def prefixEnd_2304901 : Nat := 4983230072969 + 3 ^ 40 * 2304901 * 2
def baseEnd_2304901 : Nat := 394507358009597265979153

theorem tailTrace_2304901 : CollatzResearch.WordTrace tailWord_2304901 prefixEnd_2304901 394507358009597265979153 := by
  unfold tailWord_2304901
  simp only [CollatzResearch.WordTrace]
  refine ⟨84066645822744797596170557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56044430548496531730780371 84066645822744797596170557)
  ·
    refine ⟨31524992183529299098563959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84066645822744797596170557 31524992183529299098563959)
    ·
      refine ⟨47287488275293948647845939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31524992183529299098563959 47287488275293948647845939)
      ·
        refine ⟨70931232412940922971768909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47287488275293948647845939 70931232412940922971768909)
        ·
          refine ⟨26599212154852846114413341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70931232412940922971768909 26599212154852846114413341)
          ·
            refine ⟨9974704558069817292905003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26599212154852846114413341 9974704558069817292905003)
            ·
              refine ⟨14962056837104725939357505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9974704558069817292905003 14962056837104725939357505)
              ·
                refine ⟨11221542627828544454518129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14962056837104725939357505 11221542627828544454518129)
                ·
                  refine ⟨8416156970871408340888597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11221542627828544454518129 8416156970871408340888597)
                  ·
                    refine ⟨394507358009597265979153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8416156970871408340888597 394507358009597265979153)
                    ·
                      rfl

theorem cell23_2304901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_2304901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304901 prefixEnd_2304901 := by exact prefixLift 2304901
  have htrace : WordTrace (prefixWord ++ tailWord_2304901) baseStart_2304901 baseEnd_2304901 := by
    simpa [prefixWord, tailWord_2304901, baseEnd_2304901] using wordTrace_append hprefix tailTrace_2304901
  have hstable : (prefixWord ++ tailWord_2304901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304901).length < 2 ^ (prefixWord ++ tailWord_2304901).sum := by decide
  have hdescent : baseEnd_2304901 < baseStart_2304901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304908 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 3, 4, 2]
def baseStart_2304908 : Nat := 118140960795 + 2304908 * 2 ^ 59
def prefixEnd_2304908 : Nat := 4983230072969 + 3 ^ 40 * 2304908 * 2
def baseEnd_2304908 : Nat := 1183525668393373270549927

theorem tailTrace_2304908 : CollatzResearch.WordTrace tailWord_2304908 prefixEnd_2304908 1183525668393373270549927 := by
  unfold tailWord_2304908
  simp only [CollatzResearch.WordTrace]
  refine ⟨42033450566859718895837689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56044600755812958527783585 42033450566859718895837689)
  ·
    refine ⟨31525087925144789171878267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42033450566859718895837689 31525087925144789171878267)
    ·
      refine ⟨47287631887717183757817401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31525087925144789171878267 47287631887717183757817401)
      ·
        refine ⟨35465723915787887818363051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47287631887717183757817401 35465723915787887818363051)
        ·
          refine ⟨53198585873681831727544577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35465723915787887818363051 53198585873681831727544577)
          ·
            refine ⟨39898939405261373795658433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53198585873681831727544577 39898939405261373795658433)
            ·
              refine ⟨29924204553946030346743825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39898939405261373795658433 29924204553946030346743825)
              ·
                refine ⟨22443153415459522760057869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29924204553946030346743825 22443153415459522760057869)
                ·
                  refine ⟨8416182530797321035021701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22443153415459522760057869 8416182530797321035021701)
                  ·
                    refine ⟨1578034224524497694066569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8416182530797321035021701 1578034224524497694066569)
                    ·
                      refine ⟨1183525668393373270549927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578034224524497694066569 1183525668393373270549927)
                      ·
                        rfl

theorem cell23_2304908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_2304908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304908 prefixEnd_2304908 := by exact prefixLift 2304908
  have htrace : WordTrace (prefixWord ++ tailWord_2304908) baseStart_2304908 baseEnd_2304908 := by
    simpa [prefixWord, tailWord_2304908, baseEnd_2304908] using wordTrace_append hprefix tailTrace_2304908
  have hstable : (prefixWord ++ tailWord_2304908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304908).length < 2 ^ (prefixWord ++ tailWord_2304908).sum := by decide
  have hdescent : baseEnd_2304908 < baseStart_2304908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304931 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 7]
def baseStart_2304931 : Nat := 118140960795 + 2304931 * 2 ^ 59
def prefixEnd_2304931 : Nat := 4983230072969 + 3 ^ 40 * 2304931 * 2
def baseEnd_2304931 : Nat := 131504164272047408951369

theorem tailTrace_2304931 : CollatzResearch.WordTrace tailWord_2304931 prefixEnd_2304931 131504164272047408951369 := by
  unfold tailWord_2304931
  simp only [CollatzResearch.WordTrace]
  refine ⟨84067740012636112719762647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56045160008424075146508431 84067740012636112719762647)
  ·
    refine ⟨126101610018954169079643971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84067740012636112719762647 126101610018954169079643971)
    ·
      refine ⟨189152415028431253619465957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126101610018954169079643971 189152415028431253619465957)
      ·
        refine ⟨35466077817830860053649867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189152415028431253619465957 35466077817830860053649867)
        ·
          refine ⟨53199116726746290080474801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35466077817830860053649867 53199116726746290080474801)
          ·
            refine ⟨39899337545059717560356101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53199116726746290080474801 39899337545059717560356101)
            ·
              refine ⟨7481125789698697042566769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39899337545059717560356101 7481125789698697042566769)
              ·
                refine ⟨5610844342274022781925077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7481125789698697042566769 5610844342274022781925077)
                ·
                  refine ⟨131504164272047408951369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5610844342274022781925077 131504164272047408951369)
                  ·
                    rfl

theorem cell23_2304931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 7].length) (baseStart_2304931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304931 prefixEnd_2304931 := by exact prefixLift 2304931
  have htrace : WordTrace (prefixWord ++ tailWord_2304931) baseStart_2304931 baseEnd_2304931 := by
    simpa [prefixWord, tailWord_2304931, baseEnd_2304931] using wordTrace_append hprefix tailTrace_2304931
  have hstable : (prefixWord ++ tailWord_2304931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304931).length < 2 ^ (prefixWord ++ tailWord_2304931).sum := by decide
  have hdescent : baseEnd_2304931 < baseStart_2304931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304971 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 7]
def baseStart_2304971 : Nat := 118140960795 + 2304971 * 2 ^ 59
def prefixEnd_2304971 : Nat := 4983230072969 + 3 ^ 40 * 2304971 * 2
def baseEnd_2304971 : Nat := 1183558017674606524062137

theorem tailTrace_2304971 : CollatzResearch.WordTrace tailWord_2304971 prefixEnd_2304971 1183558017674606524062137 := by
  unfold tailWord_2304971
  simp only [CollatzResearch.WordTrace]
  refine ⟨84069198932491199551218767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56046132621660799700812511 84069198932491199551218767)
  ·
    refine ⟨126103798398736799326828151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84069198932491199551218767 126103798398736799326828151)
    ·
      refine ⟨189155697598105198990242227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126103798398736799326828151 189155697598105198990242227)
      ·
        refine ⟨283733546397157798485363341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189155697598105198990242227 283733546397157798485363341)
        ·
          refine ⟨106400079898934174432011253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283733546397157798485363341 106400079898934174432011253)
          ·
            refine ⟨9975007490525078853001055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106400079898934174432011253 9975007490525078853001055)
            ·
              refine ⟨14962511235787618279501583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9975007490525078853001055 14962511235787618279501583)
              ·
                refine ⟨22443766853681427419252375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14962511235787618279501583 22443766853681427419252375)
                ·
                  refine ⟨33665650280522141128878563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22443766853681427419252375 33665650280522141128878563)
                  ·
                    refine ⟨50498475420783211693317845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33665650280522141128878563 50498475420783211693317845)
                    ·
                      refine ⟨1183558017674606524062137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50498475420783211693317845 1183558017674606524062137)
                      ·
                        rfl

theorem cell23_2304971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_2304971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304971 prefixEnd_2304971 := by exact prefixLift 2304971
  have htrace : WordTrace (prefixWord ++ tailWord_2304971) baseStart_2304971 baseEnd_2304971 := by
    simpa [prefixWord, tailWord_2304971, baseEnd_2304971] using wordTrace_append hprefix tailTrace_2304971
  have hstable : (prefixWord ++ tailWord_2304971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304971).length < 2 ^ (prefixWord ++ tailWord_2304971).sum := by decide
  have hdescent : baseEnd_2304971 < baseStart_2304971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305075 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 4, 3, 2]
def baseStart_2305075 : Nat := 118140960795 + 2305075 * 2 ^ 59
def prefixEnd_2305075 : Nat := 4983230072969 + 3 ^ 40 * 2305075 * 2
def baseEnd_2305075 : Nat := 1183611419662674117161659

theorem tailTrace_2305075 : CollatzResearch.WordTrace tailWord_2305075 prefixEnd_2305075 1183611419662674117161659 := by
  unfold tailWord_2305075
  simp only [CollatzResearch.WordTrace]
  refine ⟨84072992124114425313004679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56048661416076283542003119 84072992124114425313004679)
  ·
    refine ⟨126109488186171637969507019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84072992124114425313004679 126109488186171637969507019)
    ·
      refine ⟨189164232279257456954260529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126109488186171637969507019 189164232279257456954260529)
      ·
        refine ⟨141873174209443092715695397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189164232279257456954260529 141873174209443092715695397)
        ·
          refine ⟨26601220164270579884192887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141873174209443092715695397 26601220164270579884192887)
          ·
            refine ⟨39901830246405869826289331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26601220164270579884192887 39901830246405869826289331)
            ·
              refine ⟨59852745369608804739433997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39901830246405869826289331 59852745369608804739433997)
              ·
                refine ⟨22444779513603301777287749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59852745369608804739433997 22444779513603301777287749)
                ·
                  refine ⟨4208396158800619083241453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22444779513603301777287749 4208396158800619083241453)
                  ·
                    refine ⟨1578148559550232156215545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4208396158800619083241453 1578148559550232156215545)
                    ·
                      refine ⟨1183611419662674117161659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578148559550232156215545 1183611419662674117161659)
                      ·
                        rfl

theorem cell23_2305075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 3, 2].length) (baseStart_2305075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305075 prefixEnd_2305075 := by exact prefixLift 2305075
  have htrace : WordTrace (prefixWord ++ tailWord_2305075) baseStart_2305075 baseEnd_2305075 := by
    simpa [prefixWord, tailWord_2305075, baseEnd_2305075] using wordTrace_append hprefix tailTrace_2305075
  have hstable : (prefixWord ++ tailWord_2305075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305075).length < 2 ^ (prefixWord ++ tailWord_2305075).sum := by decide
  have hdescent : baseEnd_2305075 < baseStart_2305075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305105 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_2305105 : Nat := 118140960795 + 2305105 * 2 ^ 59
def prefixEnd_2305105 : Nat := 4983230072969 + 3 ^ 40 * 2305105 * 2
def baseEnd_2305105 : Nat := 1183626824082308999786521

theorem tailTrace_2305105 : CollatzResearch.WordTrace tailWord_2305105 prefixEnd_2305105 1183626824082308999786521 := by
  unfold tailWord_2305105
  simp only [CollatzResearch.WordTrace]
  refine ⟨84074086314005740436596769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56049390876003826957731179 84074086314005740436596769)
  ·
    refine ⟨63055564735504305327447577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84074086314005740436596769 63055564735504305327447577)
    ·
      refine ⟨47291673551628228995585683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63055564735504305327447577 47291673551628228995585683)
      ·
        refine ⟨70937510327442343493378525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47291673551628228995585683 70937510327442343493378525)
        ·
          refine ⟨26601566372790878810016947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70937510327442343493378525 26601566372790878810016947)
          ·
            refine ⟨39902349559186318215025421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26601566372790878810016947 39902349559186318215025421)
            ·
              refine ⟨14963381084694869330634533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39902349559186318215025421 14963381084694869330634533)
              ·
                refine ⟨2805633953380287999493975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14963381084694869330634533 2805633953380287999493975)
                ·
                  refine ⟨4208450930070431999240963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805633953380287999493975 4208450930070431999240963)
                  ·
                    refine ⟨6312676395105647998861445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4208450930070431999240963 6312676395105647998861445)
                    ·
                      refine ⟨1183626824082308999786521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6312676395105647998861445 1183626824082308999786521)
                      ·
                        rfl

theorem cell23_2305105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_2305105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305105 prefixEnd_2305105 := by exact prefixLift 2305105
  have htrace : WordTrace (prefixWord ++ tailWord_2305105) baseStart_2305105 baseEnd_2305105 := by
    simpa [prefixWord, tailWord_2305105, baseEnd_2305105] using wordTrace_append hprefix tailTrace_2305105
  have hstable : (prefixWord ++ tailWord_2305105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305105).length < 2 ^ (prefixWord ++ tailWord_2305105).sum := by decide
  have hdescent : baseEnd_2305105 < baseStart_2305105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305110 : List Nat := [5, 2, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2305110 : Nat := 118140960795 + 2305110 * 2 ^ 59
def prefixEnd_2305110 : Nat := 4983230072969 + 3 ^ 40 * 2305110 * 2
def baseEnd_2305110 : Nat := 394543130495193826741333

theorem tailTrace_2305110 : CollatzResearch.WordTrace tailWord_2305110 prefixEnd_2305110 394543130495193826741333 := by
  unfold tailWord_2305110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254641792436726643158049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56049512452658417527019189 5254641792436726643158049)
  ·
    refine ⟨3940981344327544982368537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5254641792436726643158049 3940981344327544982368537)
    ·
      refine ⟨2955736008245658736776403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3940981344327544982368537 2955736008245658736776403)
      ·
        refine ⟨4433604012368488105164605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955736008245658736776403 4433604012368488105164605)
        ·
          refine ⟨1662601504638183039436727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4433604012368488105164605 1662601504638183039436727)
          ·
            refine ⟨2493902256957274559155091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662601504638183039436727 2493902256957274559155091)
            ·
              refine ⟨3740853385435911838732637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493902256957274559155091 3740853385435911838732637)
              ·
                refine ⟨1402820019538466939524739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3740853385435911838732637 1402820019538466939524739)
                ·
                  refine ⟨2104230029307700409287109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402820019538466939524739 2104230029307700409287109)
                  ·
                    refine ⟨394543130495193826741333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2104230029307700409287109 394543130495193826741333)
                    ·
                      rfl

theorem cell23_2305110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2305110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305110 prefixEnd_2305110 := by exact prefixLift 2305110
  have htrace : WordTrace (prefixWord ++ tailWord_2305110) baseStart_2305110 baseEnd_2305110 := by
    simpa [prefixWord, tailWord_2305110, baseEnd_2305110] using wordTrace_append hprefix tailTrace_2305110
  have hstable : (prefixWord ++ tailWord_2305110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305110).length < 2 ^ (prefixWord ++ tailWord_2305110).sum := by decide
  have hdescent : baseEnd_2305110 < baseStart_2305110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305125 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_2305125 : Nat := 118140960795 + 2305125 * 2 ^ 59
def prefixEnd_2305125 : Nat := 4983230072969 + 3 ^ 40 * 2305125 * 2
def baseEnd_2305125 : Nat := 1183637093695398921536429

theorem tailTrace_2305125 : CollatzResearch.WordTrace tailWord_2305125 prefixEnd_2305125 1183637093695398921536429 := by
  unfold tailWord_2305125
  simp only [CollatzResearch.WordTrace]
  refine ⟨84074815773933283852324829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56049877182622189234883219 84074815773933283852324829)
  ·
    refine ⟨31528055915224981444621811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84074815773933283852324829 31528055915224981444621811)
    ·
      refine ⟨47292083872837472166932717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31528055915224981444621811 47292083872837472166932717)
      ·
        refine ⟨17734531452314052062599769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47292083872837472166932717 17734531452314052062599769)
        ·
          refine ⟨13300898589235539046949827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17734531452314052062599769 13300898589235539046949827)
          ·
            refine ⟨19951347883853308570424741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13300898589235539046949827 19951347883853308570424741)
            ·
              refine ⟨3740877728222495356954639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19951347883853308570424741 3740877728222495356954639)
              ·
                refine ⟨5611316592333743035431959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3740877728222495356954639 5611316592333743035431959)
                ·
                  refine ⟨8416974888500614553147939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5611316592333743035431959 8416974888500614553147939)
                  ·
                    refine ⟨12625462332750921829721909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8416974888500614553147939 12625462332750921829721909)
                    ·
                      refine ⟨1183637093695398921536429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12625462332750921829721909 1183637093695398921536429)
                      ·
                        rfl

theorem cell23_2305125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_2305125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305125 prefixEnd_2305125 := by exact prefixLift 2305125
  have htrace : WordTrace (prefixWord ++ tailWord_2305125) baseStart_2305125 baseEnd_2305125 := by
    simpa [prefixWord, tailWord_2305125, baseEnd_2305125] using wordTrace_append hprefix tailTrace_2305125
  have hstable : (prefixWord ++ tailWord_2305125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305125).length < 2 ^ (prefixWord ++ tailWord_2305125).sum := by decide
  have hdescent : baseEnd_2305125 < baseStart_2305125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305142 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2305142 : Nat := 118140960795 + 2305142 * 2 ^ 59
def prefixEnd_2305142 : Nat := 4983230072969 + 3 ^ 40 * 2305142 * 2
def baseEnd_2305142 : Nat := 1183645822866525355023851

theorem tailTrace_2305142 : CollatzResearch.WordTrace tailWord_2305142 prefixEnd_2305142 1183645822866525355023851 := by
  unfold tailWord_2305142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254714738429480984730855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56050290543247797170462453 5254714738429480984730855)
  ·
    refine ⟨7882072107644221477096283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5254714738429480984730855 7882072107644221477096283)
    ·
      refine ⟨11823108161466332215644425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7882072107644221477096283 11823108161466332215644425)
      ·
        refine ⟨8867331121099749161733319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11823108161466332215644425 8867331121099749161733319)
        ·
          refine ⟨13300996681649623742599979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8867331121099749161733319 13300996681649623742599979)
          ·
            refine ⟨19951495022474435613899969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13300996681649623742599979 19951495022474435613899969)
            ·
              refine ⟨14963621266855826710424977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19951495022474435613899969 14963621266855826710424977)
              ·
                refine ⟨11222715950141870032818733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14963621266855826710424977 11222715950141870032818733)
                ·
                  refine ⟨4208518481303201262307025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11222715950141870032818733 4208518481303201262307025)
                  ·
                    refine ⟨3156388860977400946730269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4208518481303201262307025 3156388860977400946730269)
                    ·
                      refine ⟨1183645822866525355023851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3156388860977400946730269 1183645822866525355023851)
                      ·
                        rfl

theorem cell23_2305142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2305142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305142 prefixEnd_2305142 := by exact prefixLift 2305142
  have htrace : WordTrace (prefixWord ++ tailWord_2305142) baseStart_2305142 baseEnd_2305142 := by
    simpa [prefixWord, tailWord_2305142, baseEnd_2305142] using wordTrace_append hprefix tailTrace_2305142
  have hstable : (prefixWord ++ tailWord_2305142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305142).length < 2 ^ (prefixWord ++ tailWord_2305142).sum := by decide
  have hdescent : baseEnd_2305142 < baseStart_2305142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305145 : List Nat := [1, 2, 1, 3, 5, 1, 2, 8]
def baseStart_2305145 : Nat := 118140960795 + 2305145 * 2 ^ 59
def prefixEnd_2305145 : Nat := 4983230072969 + 3 ^ 40 * 2305145 * 2
def baseEnd_2305145 : Nat := 43838791233647734936531

theorem tailTrace_2305145 : CollatzResearch.WordTrace tailWord_2305145 prefixEnd_2305145 43838791233647734936531 := by
  unfold tailWord_2305145
  simp only [CollatzResearch.WordTrace]
  refine ⟨84075545233860827268052889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56050363489240551512035259 84075545233860827268052889)
  ·
    refine ⟨63056658925395620451039667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84075545233860827268052889 63056658925395620451039667)
    ·
      refine ⟨94584988388093430676559501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63056658925395620451039667 94584988388093430676559501)
      ·
        refine ⟨35469370645535036503709813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94584988388093430676559501 35469370645535036503709813)
        ·
          refine ⟨3325253498018909672222795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35469370645535036503709813 3325253498018909672222795)
          ·
            refine ⟨4987880247028364508334193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325253498018909672222795 4987880247028364508334193)
            ·
              refine ⟨3740910185271273381250645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4987880247028364508334193 3740910185271273381250645)
              ·
                refine ⟨43838791233647734936531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3740910185271273381250645 43838791233647734936531)
                ·
                  rfl

theorem cell23_2305145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 8].length) (baseStart_2305145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305145 prefixEnd_2305145 := by exact prefixLift 2305145
  have htrace : WordTrace (prefixWord ++ tailWord_2305145) baseStart_2305145 baseEnd_2305145 := by
    simpa [prefixWord, tailWord_2305145, baseEnd_2305145] using wordTrace_append hprefix tailTrace_2305145
  have hstable : (prefixWord ++ tailWord_2305145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305145).length < 2 ^ (prefixWord ++ tailWord_2305145).sum := by decide
  have hdescent : baseEnd_2305145 < baseStart_2305145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305148 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2305148 : Nat := 118140960795 + 2305148 * 2 ^ 59
def prefixEnd_2305148 : Nat := 4983230072969 + 3 ^ 40 * 2305148 * 2
def baseEnd_2305148 : Nat := 1183648903750452331548823

theorem tailTrace_2305148 : CollatzResearch.WordTrace tailWord_2305148 prefixEnd_2305148 1183648903750452331548823 := by
  unfold tailWord_2305148
  simp only [CollatzResearch.WordTrace]
  refine ⟨42037827326424979390206049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56050436435233305853608065 42037827326424979390206049)
  ·
    refine ⟨31528370494818734542654537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42037827326424979390206049 31528370494818734542654537)
    ·
      refine ⟨23646277871114050906990903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31528370494818734542654537 23646277871114050906990903)
      ·
        refine ⟨35469416806671076360486355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23646277871114050906990903 35469416806671076360486355)
        ·
          refine ⟨53204125210006614540729533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35469416806671076360486355 53204125210006614540729533)
          ·
            refine ⟨19951546953752480452773575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53204125210006614540729533 19951546953752480452773575)
            ·
              refine ⟨29927320430628720679160363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19951546953752480452773575 29927320430628720679160363)
              ·
                refine ⟨44890980645943081018740545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29927320430628720679160363 44890980645943081018740545)
                ·
                  refine ⟨33668235484457310764055409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44890980645943081018740545 33668235484457310764055409)
                  ·
                    refine ⟨25251176613342983073041557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33668235484457310764055409 25251176613342983073041557)
                    ·
                      refine ⟨1183648903750452331548823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25251176613342983073041557 1183648903750452331548823)
                      ·
                        rfl

theorem cell23_2305148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2305148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305148 prefixEnd_2305148 := by exact prefixLift 2305148
  have htrace : WordTrace (prefixWord ++ tailWord_2305148) baseStart_2305148 baseEnd_2305148 := by
    simpa [prefixWord, tailWord_2305148, baseEnd_2305148] using wordTrace_append hprefix tailTrace_2305148
  have hstable : (prefixWord ++ tailWord_2305148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305148).length < 2 ^ (prefixWord ++ tailWord_2305148).sum := by decide
  have hdescent : baseEnd_2305148 < baseStart_2305148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305155 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 3]
def baseStart_2305155 : Nat := 118140960795 + 2305155 * 2 ^ 59
def prefixEnd_2305155 : Nat := 4983230072969 + 3 ^ 40 * 2305155 * 2
def baseEnd_2305155 : Nat := 1183652498115033804161291

theorem tailTrace_2305155 : CollatzResearch.WordTrace tailWord_2305155 prefixEnd_2305155 1183652498115033804161291 := by
  unfold tailWord_2305155
  simp only [CollatzResearch.WordTrace]
  refine ⟨84075909963824598975916919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56050606642549732650611279 84075909963824598975916919)
  ·
    refine ⟨126113864945736898463875379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84075909963824598975916919 126113864945736898463875379)
    ·
      refine ⟨189170797418605347695813069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126113864945736898463875379 189170797418605347695813069)
      ·
        refine ⟨70939049031977005385929901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189170797418605347695813069 70939049031977005385929901)
        ·
          refine ⟨26602143386991377019723713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70939049031977005385929901 26602143386991377019723713)
          ·
            refine ⟨19951607540243532764792785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26602143386991377019723713 19951607540243532764792785)
            ·
              refine ⟨14963705655182649573594589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19951607540243532764792785 14963705655182649573594589)
              ·
                refine ⟨5611389620693493590097971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14963705655182649573594589 5611389620693493590097971)
                ·
                  refine ⟨8417084431040240385146957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5611389620693493590097971 8417084431040240385146957)
                  ·
                    refine ⟨3156406661640090144430109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8417084431040240385146957 3156406661640090144430109)
                    ·
                      refine ⟨1183652498115033804161291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3156406661640090144430109 1183652498115033804161291)
                      ·
                        rfl

theorem cell23_2305155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_2305155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305155 prefixEnd_2305155 := by exact prefixLift 2305155
  have htrace : WordTrace (prefixWord ++ tailWord_2305155) baseStart_2305155 baseEnd_2305155 := by
    simpa [prefixWord, tailWord_2305155, baseEnd_2305155] using wordTrace_append hprefix tailTrace_2305155
  have hstable : (prefixWord ++ tailWord_2305155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305155).length < 2 ^ (prefixWord ++ tailWord_2305155).sum := by decide
  have hdescent : baseEnd_2305155 < baseStart_2305155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305168 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_2305168 : Nat := 118140960795 + 2305168 * 2 ^ 59
def prefixEnd_2305168 : Nat := 4983230072969 + 3 ^ 40 * 2305168 * 2
def baseEnd_2305168 : Nat := 1183659173363542253298731

theorem tailTrace_2305168 : CollatzResearch.WordTrace tailWord_2305168 prefixEnd_2305168 1183659173363542253298731 := by
  unfold tailWord_2305168
  simp only [CollatzResearch.WordTrace]
  refine ⟨42038192056388751098070079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56050922741851668130760105 42038192056388751098070079)
  ·
    refine ⟨63057288084583126647105119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42038192056388751098070079 63057288084583126647105119)
    ·
      refine ⟨94585932126874689970657679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63057288084583126647105119 94585932126874689970657679)
      ·
        refine ⟨141878898190312034955986519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94585932126874689970657679 141878898190312034955986519)
        ·
          refine ⟨212818347285468052433979779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141878898190312034955986519 212818347285468052433979779)
          ·
            refine ⟨319227520928202078650969669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212818347285468052433979779 319227520928202078650969669)
            ·
              refine ⟨59855160174037889747056813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 319227520928202078650969669 59855160174037889747056813)
              ·
                refine ⟨22445685065264208655146305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59855160174037889747056813 22445685065264208655146305)
                ·
                  refine ⟨16834263798948156491359729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22445685065264208655146305 16834263798948156491359729)
                  ·
                    refine ⟨12625697849211117368519797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16834263798948156491359729 12625697849211117368519797)
                    ·
                      refine ⟨1183659173363542253298731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12625697849211117368519797 1183659173363542253298731)
                      ·
                        rfl

theorem cell23_2305168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_2305168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305168 prefixEnd_2305168 := by exact prefixLift 2305168
  have htrace : WordTrace (prefixWord ++ tailWord_2305168) baseStart_2305168 baseEnd_2305168 := by
    simpa [prefixWord, tailWord_2305168, baseEnd_2305168] using wordTrace_append hprefix tailTrace_2305168
  have hstable : (prefixWord ++ tailWord_2305168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305168).length < 2 ^ (prefixWord ++ tailWord_2305168).sum := by decide
  have hdescent : baseEnd_2305168 < baseStart_2305168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305189 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_2305189 : Nat := 118140960795 + 2305189 * 2 ^ 59
def prefixEnd_2305189 : Nat := 4983230072969 + 3 ^ 40 * 2305189 * 2
def baseEnd_2305189 : Nat := 1183669956457286671136135

theorem tailTrace_2305189 : CollatzResearch.WordTrace tailWord_2305189 prefixEnd_2305189 1183669956457286671136135 := by
  unfold tailWord_2305189
  simp only [CollatzResearch.WordTrace]
  refine ⟨84077150045701422782654621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56051433363800948521769747 84077150045701422782654621)
  ·
    refine ⟨31528931267138033543495483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84077150045701422782654621 31528931267138033543495483)
    ·
      refine ⟨47293396900707050315243225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31528931267138033543495483 47293396900707050315243225)
      ·
        refine ⟨35470047675530287736432419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47293396900707050315243225 35470047675530287736432419)
        ·
          refine ⟨53205071513295431604648629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35470047675530287736432419 53205071513295431604648629)
          ·
            refine ⟨4987975454371446712935809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53205071513295431604648629 4987975454371446712935809)
            ·
              refine ⟨3740981590778585034701857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4987975454371446712935809 3740981590778585034701857)
              ·
                refine ⟨2805736193083938776026393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3740981590778585034701857 2805736193083938776026393)
                ·
                  refine ⟨2104302144812954082019795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2805736193083938776026393 2104302144812954082019795)
                  ·
                    refine ⟨3156453217219431123029693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2104302144812954082019795 3156453217219431123029693)
                    ·
                      refine ⟨1183669956457286671136135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3156453217219431123029693 1183669956457286671136135)
                      ·
                        rfl

theorem cell23_2305189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_2305189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305189 prefixEnd_2305189 := by exact prefixLift 2305189
  have htrace : WordTrace (prefixWord ++ tailWord_2305189) baseStart_2305189 baseEnd_2305189 := by
    simpa [prefixWord, tailWord_2305189, baseEnd_2305189] using wordTrace_append hprefix tailTrace_2305189
  have hstable : (prefixWord ++ tailWord_2305189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305189).length < 2 ^ (prefixWord ++ tailWord_2305189).sum := by decide
  have hdescent : baseEnd_2305189 < baseStart_2305189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305252 : List Nat := [2, 3, 1, 1, 1, 2, 4, 4, 5]
def baseStart_2305252 : Nat := 118140960795 + 2305252 * 2 ^ 59
def prefixEnd_2305252 : Nat := 4983230072969 + 3 ^ 40 * 2305252 * 2
def baseEnd_2305252 : Nat := 131522478415391102738705

theorem tailTrace_2305252 : CollatzResearch.WordTrace tailWord_2305252 prefixEnd_2305252 131522478415391102738705 := by
  unfold tailWord_2305252
  simp only [CollatzResearch.WordTrace]
  refine ⟨42039723922236592271099005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56052965229648789694798673 42039723922236592271099005)
  ·
    refine ⟨15764896470838722101662127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42039723922236592271099005 15764896470838722101662127)
    ·
      refine ⟨23647344706258083152493191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15764896470838722101662127 23647344706258083152493191)
      ·
        refine ⟨35471017059387124728739787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23647344706258083152493191 35471017059387124728739787)
        ·
          refine ⟨53206525589080687093109681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35471017059387124728739787 53206525589080687093109681)
          ·
            refine ⟨39904894191810515319832261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53206525589080687093109681 39904894191810515319832261)
            ·
              refine ⟨7482167660964471622468549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39904894191810515319832261 7482167660964471622468549)
              ·
                refine ⟨1402906436430838429212853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7482167660964471622468549 1402906436430838429212853)
                ·
                  refine ⟨131522478415391102738705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1402906436430838429212853 131522478415391102738705)
                  ·
                    rfl

theorem cell23_2305252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_2305252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305252 prefixEnd_2305252 := by exact prefixLift 2305252
  have htrace : WordTrace (prefixWord ++ tailWord_2305252) baseStart_2305252 baseEnd_2305252 := by
    simpa [prefixWord, tailWord_2305252, baseEnd_2305252] using wordTrace_append hprefix tailTrace_2305252
  have hstable : (prefixWord ++ tailWord_2305252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305252).length < 2 ^ (prefixWord ++ tailWord_2305252).sum := by decide
  have hdescent : baseEnd_2305252 < baseStart_2305252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305262 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_2305262 : Nat := 118140960795 + 2305262 * 2 ^ 59
def prefixEnd_2305262 : Nat := 4983230072969 + 3 ^ 40 * 2305262 * 2
def baseEnd_2305262 : Nat := 1183707440545064885523299

theorem tailTrace_2305262 : CollatzResearch.WordTrace tailWord_2305262 prefixEnd_2305262 1183707440545064885523299 := by
  unfold tailWord_2305262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10509976571804619531257755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56053208382957970833374693 10509976571804619531257755)
  ·
    refine ⟨15764964857706929296886633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10509976571804619531257755 15764964857706929296886633)
    ·
      refine ⟨11823723643280196972664975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15764964857706929296886633 11823723643280196972664975)
      ·
        refine ⟨17735585464920295458997463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11823723643280196972664975 17735585464920295458997463)
        ·
          refine ⟨26603378197380443188496195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17735585464920295458997463 26603378197380443188496195)
          ·
            refine ⟨39905067296070664782744293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26603378197380443188496195 39905067296070664782744293)
            ·
              refine ⟨7482200118013249646764555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39905067296070664782744293 7482200118013249646764555)
              ·
                refine ⟨11223300177019874470146833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7482200118013249646764555 11223300177019874470146833)
                ·
                  refine ⟨8417475132764905852610125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11223300177019874470146833 8417475132764905852610125)
                  ·
                    refine ⟨3156553174786839694728797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8417475132764905852610125 3156553174786839694728797)
                    ·
                      refine ⟨1183707440545064885523299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3156553174786839694728797 1183707440545064885523299)
                      ·
                        rfl

theorem cell23_2305262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_2305262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305262 prefixEnd_2305262 := by exact prefixLift 2305262
  have htrace : WordTrace (prefixWord ++ tailWord_2305262) baseStart_2305262 baseEnd_2305262 := by
    simpa [prefixWord, tailWord_2305262, baseEnd_2305262] using wordTrace_append hprefix tailTrace_2305262
  have hstable : (prefixWord ++ tailWord_2305262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305262).length < 2 ^ (prefixWord ++ tailWord_2305262).sum := by decide
  have hdescent : baseEnd_2305262 < baseStart_2305262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305263 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 2, 2, 2]
def baseStart_2305263 : Nat := 118140960795 + 2305263 * 2 ^ 59
def prefixEnd_2305263 : Nat := 4983230072969 + 3 ^ 40 * 2305263 * 2
def baseEnd_2305263 : Nat := 1183707954025719381610795

theorem tailTrace_2305263 : CollatzResearch.WordTrace tailWord_2305263 prefixEnd_2305263 1183707954025719381610795 := by
  unfold tailWord_2305263
  simp only [CollatzResearch.WordTrace]
  refine ⟨84079849047433333420848443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56053232698288888947232295 84079849047433333420848443)
  ·
    refine ⟨126119773571150000131272665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84079849047433333420848443 126119773571150000131272665)
    ·
      refine ⟨94589830178362500098454499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126119773571150000131272665 94589830178362500098454499)
      ·
        refine ⟨141884745267543750147681749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94589830178362500098454499 141884745267543750147681749)
        ·
          refine ⟨3325423717208056644086291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 141884745267543750147681749 3325423717208056644086291)
          ·
            refine ⟨4988135575812084966129437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325423717208056644086291 4988135575812084966129437)
            ·
              refine ⟨1870550840929531862298539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4988135575812084966129437 1870550840929531862298539)
              ·
                refine ⟨2805826261394297793447809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1870550840929531862298539 2805826261394297793447809)
                ·
                  refine ⟨2104369696045723345085857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2805826261394297793447809 2104369696045723345085857)
                  ·
                    refine ⟨1578277272034292508814393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2104369696045723345085857 1578277272034292508814393)
                    ·
                      refine ⟨1183707954025719381610795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578277272034292508814393 1183707954025719381610795)
                      ·
                        rfl

theorem cell23_2305263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 2, 2].length) (baseStart_2305263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305263 prefixEnd_2305263 := by exact prefixLift 2305263
  have htrace : WordTrace (prefixWord ++ tailWord_2305263) baseStart_2305263 baseEnd_2305263 := by
    simpa [prefixWord, tailWord_2305263, baseEnd_2305263] using wordTrace_append hprefix tailTrace_2305263
  have hstable : (prefixWord ++ tailWord_2305263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305263).length < 2 ^ (prefixWord ++ tailWord_2305263).sum := by decide
  have hdescent : baseEnd_2305263 < baseStart_2305263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305285 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_2305285 : Nat := 118140960795 + 2305285 * 2 ^ 59
def prefixEnd_2305285 : Nat := 4983230072969 + 3 ^ 40 * 2305285 * 2
def baseEnd_2305285 : Nat := 1183719250600118295535693

theorem tailTrace_2305285 : CollatzResearch.WordTrace tailWord_2305285 prefixEnd_2305285 1183719250600118295535693 := by
  unfold tailWord_2305285
  simp only [CollatzResearch.WordTrace]
  refine ⟨84080651453353631178149309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56053767635569087452099539 84080651453353631178149309)
  ·
    refine ⟨31530244295007611691805991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84080651453353631178149309 31530244295007611691805991)
    ·
      refine ⟨47295366442511417537708987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31530244295007611691805991 47295366442511417537708987)
      ·
        refine ⟨70943049663767126306563481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47295366442511417537708987 70943049663767126306563481)
        ·
          refine ⟨53207287247825344729922611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70943049663767126306563481 53207287247825344729922611)
          ·
            refine ⟨79810930871738017094883917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53207287247825344729922611 79810930871738017094883917)
            ·
              refine ⟨29929099076901756410581469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79810930871738017094883917 29929099076901756410581469)
              ·
                refine ⟨11223412153838158653968051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29929099076901756410581469 11223412153838158653968051)
                ·
                  refine ⟨16835118230757237980952077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11223412153838158653968051 16835118230757237980952077)
                  ·
                    refine ⟨6313169336533964242857029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16835118230757237980952077 6313169336533964242857029)
                    ·
                      refine ⟨1183719250600118295535693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6313169336533964242857029 1183719250600118295535693)
                      ·
                        rfl

theorem cell23_2305285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_2305285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305285 prefixEnd_2305285 := by exact prefixLift 2305285
  have htrace : WordTrace (prefixWord ++ tailWord_2305285) baseStart_2305285 baseEnd_2305285 := by
    simpa [prefixWord, tailWord_2305285, baseEnd_2305285] using wordTrace_append hprefix tailTrace_2305285
  have hstable : (prefixWord ++ tailWord_2305285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305285).length < 2 ^ (prefixWord ++ tailWord_2305285).sum := by decide
  have hdescent : baseEnd_2305285 < baseStart_2305285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305305 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 3]
def baseStart_2305305 : Nat := 118140960795 + 2305305 * 2 ^ 59
def prefixEnd_2305305 : Nat := 4983230072969 + 3 ^ 40 * 2305305 * 2
def baseEnd_2305305 : Nat := 1183729520213208217285601

theorem tailTrace_2305305 : CollatzResearch.WordTrace tailWord_2305305 prefixEnd_2305305 1183729520213208217285601 := by
  unfold tailWord_2305305
  simp only [CollatzResearch.WordTrace]
  refine ⟨84081380913281174593877369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56054253942187449729251579 84081380913281174593877369)
  ·
    refine ⟨63061035684960880945408027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84081380913281174593877369 63061035684960880945408027)
    ·
      refine ⟨94591553527441321418112041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63061035684960880945408027 94591553527441321418112041)
      ·
        refine ⟨70943665145580991063584031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94591553527441321418112041 70943665145580991063584031)
        ·
          refine ⟨106415497718371486595376047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70943665145580991063584031 106415497718371486595376047)
          ·
            refine ⟨159623246577557229893064071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106415497718371486595376047 159623246577557229893064071)
            ·
              refine ⟨239434869866335844839596107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159623246577557229893064071 239434869866335844839596107)
              ·
                refine ⟨359152304799503767259394161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239434869866335844839596107 359152304799503767259394161)
                ·
                  refine ⟨269364228599627825444545621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359152304799503767259394161 269364228599627825444545621)
                  ·
                    refine ⟨3156612053901888579428269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 269364228599627825444545621 3156612053901888579428269)
                    ·
                      refine ⟨1183729520213208217285601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3156612053901888579428269 1183729520213208217285601)
                      ·
                        rfl

theorem cell23_2305305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_2305305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305305 prefixEnd_2305305 := by exact prefixLift 2305305
  have htrace : WordTrace (prefixWord ++ tailWord_2305305) baseStart_2305305 baseEnd_2305305 := by
    simpa [prefixWord, tailWord_2305305, baseEnd_2305305] using wordTrace_append hprefix tailTrace_2305305
  have hstable : (prefixWord ++ tailWord_2305305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305305).length < 2 ^ (prefixWord ++ tailWord_2305305).sum := by decide
  have hdescent : baseEnd_2305305 < baseStart_2305305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305390 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_2305390 : Nat := 118140960795 + 2305390 * 2 ^ 59
def prefixEnd_2305390 : Nat := 4983230072969 + 3 ^ 40 * 2305390 * 2
def baseEnd_2305390 : Nat := 1183773166068840384722711

theorem tailTrace_2305390 : CollatzResearch.WordTrace tailWord_2305390 prefixEnd_2305390 1183773166068840384722711 := by
  unfold tailWord_2305390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10510560139746654263840203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56056320745315489407147749 10510560139746654263840203)
  ·
    refine ⟨15765840209619981395760305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10510560139746654263840203 15765840209619981395760305)
    ·
      refine ⟨11824380157214986046820229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15765840209619981395760305 11824380157214986046820229)
      ·
        refine ⟨2217071279477809883778793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11824380157214986046820229 2217071279477809883778793)
        ·
          refine ⟨1662803459608357412834095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2217071279477809883778793 1662803459608357412834095)
          ·
            refine ⟨2494205189412536119251143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662803459608357412834095 2494205189412536119251143)
            ·
              refine ⟨3741307784118804178876715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494205189412536119251143 3741307784118804178876715)
              ·
                refine ⟨5611961676178206268315073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741307784118804178876715 5611961676178206268315073)
                ·
                  refine ⟨4208971257133654701236305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5611961676178206268315073 4208971257133654701236305)
                  ·
                    refine ⟨3156728442850241025927229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4208971257133654701236305 3156728442850241025927229)
                    ·
                      refine ⟨1183773166068840384722711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3156728442850241025927229 1183773166068840384722711)
                      ·
                        rfl

theorem cell23_2305390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_2305390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305390 prefixEnd_2305390 := by exact prefixLift 2305390
  have htrace : WordTrace (prefixWord ++ tailWord_2305390) baseStart_2305390 baseEnd_2305390 := by
    simpa [prefixWord, tailWord_2305390, baseEnd_2305390] using wordTrace_append hprefix tailTrace_2305390
  have hstable : (prefixWord ++ tailWord_2305390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305390).length < 2 ^ (prefixWord ++ tailWord_2305390).sum := by decide
  have hdescent : baseEnd_2305390 < baseStart_2305390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305392 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_2305392 : Nat := 118140960795 + 2305392 * 2 ^ 59
def prefixEnd_2305392 : Nat := 4983230072969 + 3 ^ 40 * 2305392 * 2
def baseEnd_2305392 : Nat := 1183774193030149376897701

theorem tailTrace_2305392 : CollatzResearch.WordTrace tailWord_2305392 prefixEnd_2305392 1183774193030149376897701 := by
  unfold tailWord_2305392
  simp only [CollatzResearch.WordTrace]
  refine ⟨42042277031982994226147215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56056369375977325634862953 42042277031982994226147215)
  ·
    refine ⟨63063415547974491339220823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42042277031982994226147215 63063415547974491339220823)
    ·
      refine ⟨94595123321961737008831235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63063415547974491339220823 94595123321961737008831235)
      ·
        refine ⟨141892684982942605513246853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94595123321961737008831235 141892684982942605513246853)
        ·
          refine ⟨26604878434301738533733785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141892684982942605513246853 26604878434301738533733785)
          ·
            refine ⟨19953658825726303900300339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26604878434301738533733785 19953658825726303900300339)
            ·
              refine ⟨29930488238589455850450509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19953658825726303900300339 29930488238589455850450509)
              ·
                refine ⟨11223933089471045943918941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29930488238589455850450509 11223933089471045943918941)
                ·
                  refine ⟨4208974908551642228969603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11223933089471045943918941 4208974908551642228969603)
                  ·
                    refine ⟨6313462362827463343454405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4208974908551642228969603 6313462362827463343454405)
                    ·
                      refine ⟨1183774193030149376897701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6313462362827463343454405 1183774193030149376897701)
                      ·
                        rfl

theorem cell23_2305392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_2305392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305392 prefixEnd_2305392 := by exact prefixLift 2305392
  have htrace : WordTrace (prefixWord ++ tailWord_2305392) baseStart_2305392 baseEnd_2305392 := by
    simpa [prefixWord, tailWord_2305392, baseEnd_2305392] using wordTrace_append hprefix tailTrace_2305392
  have hstable : (prefixWord ++ tailWord_2305392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305392).length < 2 ^ (prefixWord ++ tailWord_2305392).sum := by decide
  have hdescent : baseEnd_2305392 < baseStart_2305392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305395 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 5]
def baseStart_2305395 : Nat := 118140960795 + 2305395 * 2 ^ 59
def prefixEnd_2305395 : Nat := 4983230072969 + 3 ^ 40 * 2305395 * 2
def baseEnd_2305395 : Nat := 1183775733472112865160187

theorem tailTrace_2305395 : CollatzResearch.WordTrace tailWord_2305395 prefixEnd_2305395 1183775733472112865160187 := by
  unfold tailWord_2305395
  simp only [CollatzResearch.WordTrace]
  refine ⟨84084663482955119964653639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56056442321970079976435759 84084663482955119964653639)
  ·
    refine ⟨126126995224432679946980459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84084663482955119964653639 126126995224432679946980459)
    ·
      refine ⟨189190492836649019920470689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126126995224432679946980459 189190492836649019920470689)
      ·
        refine ⟨141892869627486764940353017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189190492836649019920470689 141892869627486764940353017)
        ·
          refine ⟨106419652220615073705264763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141892869627486764940353017 106419652220615073705264763)
          ·
            refine ⟨159629478330922610557897145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106419652220615073705264763 159629478330922610557897145)
            ·
              refine ⟨119722108748191957918422859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159629478330922610557897145 119722108748191957918422859)
              ·
                refine ⟨179583163122287936877634289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119722108748191957918422859 179583163122287936877634289)
                ·
                  refine ⟨134687372341715952658225717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179583163122287936877634289 134687372341715952658225717)
                  ·
                    refine ⟨12626941157035870561708661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134687372341715952658225717 12626941157035870561708661)
                    ·
                      refine ⟨1183775733472112865160187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12626941157035870561708661 1183775733472112865160187)
                      ·
                        rfl

theorem cell23_2305395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_2305395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305395 prefixEnd_2305395 := by exact prefixLift 2305395
  have htrace : WordTrace (prefixWord ++ tailWord_2305395) baseStart_2305395 baseEnd_2305395 := by
    simpa [prefixWord, tailWord_2305395, baseEnd_2305395] using wordTrace_append hprefix tailTrace_2305395
  have hstable : (prefixWord ++ tailWord_2305395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305395).length < 2 ^ (prefixWord ++ tailWord_2305395).sum := by decide
  have hdescent : baseEnd_2305395 < baseStart_2305395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305402 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_2305402 : Nat := 118140960795 + 2305402 * 2 ^ 59
def prefixEnd_2305402 : Nat := 4983230072969 + 3 ^ 40 * 2305402 * 2
def baseEnd_2305402 : Nat := 394593109278898112590885

theorem tailTrace_2305402 : CollatzResearch.WordTrace tailWord_2305402 prefixEnd_2305402 394593109278898112590885 := by
  unfold tailWord_2305402
  simp only [CollatzResearch.WordTrace]
  refine ⟨21021229698482440040039615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56056612529286506773438973 21021229698482440040039615)
  ·
    refine ⟨31531844547723660060059423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21021229698482440040039615 31531844547723660060059423)
    ·
      refine ⟨47297766821585490090089135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31531844547723660060059423 47297766821585490090089135)
      ·
        refine ⟨70946650232378235135133703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47297766821585490090089135 70946650232378235135133703)
        ·
          refine ⟨106419975348567352702700555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70946650232378235135133703 106419975348567352702700555)
          ·
            refine ⟨159629963022851029054050833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106419975348567352702700555 159629963022851029054050833)
            ·
              refine ⟨119722472267138271790538125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159629963022851029054050833 119722472267138271790538125)
              ·
                refine ⟨44895927100176851921451797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119722472267138271790538125 44895927100176851921451797)
                ·
                  refine ⟨2104496582820789933818053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44895927100176851921451797 2104496582820789933818053)
                  ·
                    refine ⟨394593109278898112590885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2104496582820789933818053 394593109278898112590885)
                    ·
                      rfl

theorem cell23_2305402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_2305402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305402 prefixEnd_2305402 := by exact prefixLift 2305402
  have htrace : WordTrace (prefixWord ++ tailWord_2305402) baseStart_2305402 baseEnd_2305402 := by
    simpa [prefixWord, tailWord_2305402, baseEnd_2305402] using wordTrace_append hprefix tailTrace_2305402
  have hstable : (prefixWord ++ tailWord_2305402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305402).length < 2 ^ (prefixWord ++ tailWord_2305402).sum := by decide
  have hdescent : baseEnd_2305402 < baseStart_2305402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305439 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2305439 : Nat := 118140960795 + 2305439 * 2 ^ 59
def prefixEnd_2305439 : Nat := 4983230072969 + 3 ^ 40 * 2305439 * 2
def baseEnd_2305439 : Nat := 1183798326620910693009985

theorem tailTrace_2305439 : CollatzResearch.WordTrace tailWord_2305439 prefixEnd_2305439 1183798326620910693009985 := by
  unfold tailWord_2305439
  simp only [CollatzResearch.WordTrace]
  refine ⟨84086268294795715479255371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56057512196530476986170247 84086268294795715479255371)
  ·
    refine ⟨126129402442193573218883057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84086268294795715479255371 126129402442193573218883057)
    ·
      refine ⟨94597051831645179914162293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126129402442193573218883057 94597051831645179914162293)
      ·
        refine ⟨8868473609216735616952715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94597051831645179914162293 8868473609216735616952715)
        ·
          refine ⟨13302710413825103425429073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8868473609216735616952715 13302710413825103425429073)
          ·
            refine ⟨9977032810368827569071805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13302710413825103425429073 9977032810368827569071805)
            ·
              refine ⟨3741387303888310338401927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9977032810368827569071805 3741387303888310338401927)
              ·
                refine ⟨5612080955832465507602891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741387303888310338401927 5612080955832465507602891)
                ·
                  refine ⟨8418121433748698261404337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5612080955832465507602891 8418121433748698261404337)
                  ·
                    refine ⟨6313591075311523696053253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8418121433748698261404337 6313591075311523696053253)
                    ·
                      refine ⟨1183798326620910693009985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6313591075311523696053253 1183798326620910693009985)
                      ·
                        rfl

theorem cell23_2305439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2305439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305439 prefixEnd_2305439 := by exact prefixLift 2305439
  have htrace : WordTrace (prefixWord ++ tailWord_2305439) baseStart_2305439 baseEnd_2305439 := by
    simpa [prefixWord, tailWord_2305439, baseEnd_2305439] using wordTrace_append hprefix tailTrace_2305439
  have hstable : (prefixWord ++ tailWord_2305439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305439).length < 2 ^ (prefixWord ++ tailWord_2305439).sum := by decide
  have hdescent : baseEnd_2305439 < baseStart_2305439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305516 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 4, 2, 2]
def baseStart_2305516 : Nat := 118140960795 + 2305516 * 2 ^ 59
def prefixEnd_2305516 : Nat := 4983230072969 + 3 ^ 40 * 2305516 * 2
def baseEnd_2305516 : Nat := 1183837864631306891747131

theorem tailTrace_2305516 : CollatzResearch.WordTrace tailWord_2305516 prefixEnd_2305516 1183837864631306891747131 := by
  unfold tailWord_2305516
  simp only [CollatzResearch.WordTrace]
  refine ⟨42044538357758378814904201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56059384477011171753205601 42044538357758378814904201)
  ·
    refine ⟨31533403768318784111178151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42044538357758378814904201 31533403768318784111178151)
    ·
      refine ⟨47300105652478176166767227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31533403768318784111178151 47300105652478176166767227)
      ·
        refine ⟨70950158478717264250150841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47300105652478176166767227 70950158478717264250150841)
        ·
          refine ⟨53212618859037948187613131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70950158478717264250150841 53212618859037948187613131)
          ·
            refine ⟨79818928288556922281419697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53212618859037948187613131 79818928288556922281419697)
            ·
              refine ⟨59864196216417691711064773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79818928288556922281419697 59864196216417691711064773)
              ·
                refine ⟨11224536790578317195824645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59864196216417691711064773 11224536790578317195824645)
                ·
                  refine ⟨2104600648233434474217121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11224536790578317195824645 2104600648233434474217121)
                  ·
                    refine ⟨1578450486175075855662841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2104600648233434474217121 1578450486175075855662841)
                    ·
                      refine ⟨1183837864631306891747131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578450486175075855662841 1183837864631306891747131)
                      ·
                        rfl

theorem cell23_2305516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_2305516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305516 prefixEnd_2305516 := by exact prefixLift 2305516
  have htrace : WordTrace (prefixWord ++ tailWord_2305516) baseStart_2305516 baseEnd_2305516 := by
    simpa [prefixWord, tailWord_2305516, baseEnd_2305516] using wordTrace_append hprefix tailTrace_2305516
  have hstable : (prefixWord ++ tailWord_2305516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305516).length < 2 ^ (prefixWord ++ tailWord_2305516).sum := by decide
  have hdescent : baseEnd_2305516 < baseStart_2305516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305532 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2305532 : Nat := 118140960795 + 2305532 * 2 ^ 59
def prefixEnd_2305532 : Nat := 4983230072969 + 3 ^ 40 * 2305532 * 2
def baseEnd_2305532 : Nat := 1183846080321778829147057

theorem tailTrace_2305532 : CollatzResearch.WordTrace tailWord_2305532 prefixEnd_2305532 1183846080321778829147057 := by
  unfold tailWord_2305532
  simp only [CollatzResearch.WordTrace]
  refine ⟨42044830141729396181195425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56059773522305861574927233 42044830141729396181195425)
  ·
    refine ⟨31533622606297047135896569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42044830141729396181195425 31533622606297047135896569)
    ·
      refine ⟨23650216954722785351922427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31533622606297047135896569 23650216954722785351922427)
      ·
        refine ⟨35475325432084178027883641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23650216954722785351922427 35475325432084178027883641)
        ·
          refine ⟨26606494074063133520912731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35475325432084178027883641 26606494074063133520912731)
          ·
            refine ⟨39909741111094700281369097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26606494074063133520912731 39909741111094700281369097)
            ·
              refine ⟨29932305833321025211026823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39909741111094700281369097 29932305833321025211026823)
              ·
                refine ⟨44898458749981537816540235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29932305833321025211026823 44898458749981537816540235)
                ·
                  refine ⟨67347688124972306724810353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44898458749981537816540235 67347688124972306724810353)
                  ·
                    refine ⟨50510766093729230043607765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67347688124972306724810353 50510766093729230043607765)
                    ·
                      refine ⟨1183846080321778829147057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50510766093729230043607765 1183846080321778829147057)
                      ·
                        rfl

theorem cell23_2305532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2305532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305532 prefixEnd_2305532 := by exact prefixLift 2305532
  have htrace : WordTrace (prefixWord ++ tailWord_2305532) baseStart_2305532 baseEnd_2305532 := by
    simpa [prefixWord, tailWord_2305532, baseEnd_2305532] using wordTrace_append hprefix tailTrace_2305532
  have hstable : (prefixWord ++ tailWord_2305532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305532).length < 2 ^ (prefixWord ++ tailWord_2305532).sum := by decide
  have hdescent : baseEnd_2305532 < baseStart_2305532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305533 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_2305533 : Nat := 118140960795 + 2305533 * 2 ^ 59
def prefixEnd_2305533 : Nat := 4983230072969 + 3 ^ 40 * 2305533 * 2
def baseEnd_2305533 : Nat := 1183846593802433325234553

theorem tailTrace_2305533 : CollatzResearch.WordTrace tailWord_2305533 prefixEnd_2305533 1183846593802433325234553 := by
  unfold tailWord_2305533
  simp only [CollatzResearch.WordTrace]
  refine ⟨84089696756455169533177253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56059797837636779688784835 84089696756455169533177253)
  ·
    refine ⟨15766818141835344287470735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84089696756455169533177253 15766818141835344287470735)
    ·
      refine ⟨23650227212753016431206103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15766818141835344287470735 23650227212753016431206103)
      ·
        refine ⟨35475340819129524646809155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23650227212753016431206103 35475340819129524646809155)
        ·
          refine ⟨53213011228694286970213733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35475340819129524646809155 53213011228694286970213733)
          ·
            refine ⟨9977439605380178806915075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53213011228694286970213733 9977439605380178806915075)
            ·
              refine ⟨14966159408070268210372613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9977439605380178806915075 14966159408070268210372613)
              ·
                refine ⟨2806154889013175289444865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14966159408070268210372613 2806154889013175289444865)
                ·
                  refine ⟨2104616166759881467083649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2806154889013175289444865 2104616166759881467083649)
                  ·
                    refine ⟨1578462125069911100312737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2104616166759881467083649 1578462125069911100312737)
                    ·
                      refine ⟨1183846593802433325234553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578462125069911100312737 1183846593802433325234553)
                      ·
                        rfl

theorem cell23_2305533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_2305533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305533 prefixEnd_2305533 := by exact prefixLift 2305533
  have htrace : WordTrace (prefixWord ++ tailWord_2305533) baseStart_2305533 baseEnd_2305533 := by
    simpa [prefixWord, tailWord_2305533, baseEnd_2305533] using wordTrace_append hprefix tailTrace_2305533
  have hstable : (prefixWord ++ tailWord_2305533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305533).length < 2 ^ (prefixWord ++ tailWord_2305533).sum := by decide
  have hdescent : baseEnd_2305533 < baseStart_2305533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305569 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 1, 7]
def baseStart_2305569 : Nat := 118140960795 + 2305569 * 2 ^ 59
def prefixEnd_2305569 : Nat := 4983230072969 + 3 ^ 40 * 2305569 * 2
def baseEnd_2305569 : Nat := 394621693035331728128129

theorem tailTrace_2305569 : CollatzResearch.WordTrace tailWord_2305569 prefixEnd_2305569 394621693035331728128129 := by
  unfold tailWord_2305569
  simp only [CollatzResearch.WordTrace]
  refine ⟨84091009784324747681487761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56060673189549831787658507 84091009784324747681487761)
  ·
    refine ⟨63068257338243560761115821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84091009784324747681487761 63068257338243560761115821)
    ·
      refine ⟨23650596501841335285418433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63068257338243560761115821 23650596501841335285418433)
      ·
        refine ⟨17737947376381001464063825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23650596501841335285418433 17737947376381001464063825)
        ·
          refine ⟨13303460532285751098047869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17737947376381001464063825 13303460532285751098047869)
          ·
            refine ⟨4988797699607156661767951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13303460532285751098047869 4988797699607156661767951)
            ·
              refine ⟨7483196549410734992651927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4988797699607156661767951 7483196549410734992651927)
              ·
                refine ⟨11224794824116102488977891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7483196549410734992651927 11224794824116102488977891)
                ·
                  refine ⟨16837192236174153733466837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11224794824116102488977891 16837192236174153733466837)
                  ·
                    refine ⟨394621693035331728128129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16837192236174153733466837 394621693035331728128129)
                    ·
                      rfl

theorem cell23_2305569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_2305569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305569 prefixEnd_2305569 := by exact prefixLift 2305569
  have htrace : WordTrace (prefixWord ++ tailWord_2305569) baseStart_2305569 baseEnd_2305569 := by
    simpa [prefixWord, tailWord_2305569, baseEnd_2305569] using wordTrace_append hprefix tailTrace_2305569
  have hstable : (prefixWord ++ tailWord_2305569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305569).length < 2 ^ (prefixWord ++ tailWord_2305569).sum := by decide
  have hdescent : baseEnd_2305569 < baseStart_2305569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305659 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 3, 5]
def baseStart_2305659 : Nat := 118140960795 + 2305659 * 2 ^ 59
def prefixEnd_2305659 : Nat := 4983230072969 + 3 ^ 40 * 2305659 * 2
def baseEnd_2305659 : Nat := 394637097454966610752991

theorem tailTrace_2305659 : CollatzResearch.WordTrace tailWord_2305659 prefixEnd_2305659 394637097454966610752991 := by
  unfold tailWord_2305659
  simp only [CollatzResearch.WordTrace]
  refine ⟨84094292353998693052264031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56062861569332462034842687 84094292353998693052264031)
  ·
    refine ⟨126141438530998039578396047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84094292353998693052264031 126141438530998039578396047)
    ·
      refine ⟨189212157796497059367594071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126141438530998039578396047 189212157796497059367594071)
      ·
        refine ⟨283818236694745589051391107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189212157796497059367594071 283818236694745589051391107)
        ·
          refine ⟨425727355042118383577086661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283818236694745589051391107 425727355042118383577086661)
          ·
            refine ⟨79823879070397196920703749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 425727355042118383577086661 79823879070397196920703749)
            ·
              refine ⟨14966977325699474422631953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79823879070397196920703749 14966977325699474422631953)
              ·
                refine ⟨11225232994274605816973965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14966977325699474422631953 11225232994274605816973965)
                ·
                  refine ⟨4209462372852977181365237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11225232994274605816973965 4209462372852977181365237)
                  ·
                    refine ⟨394637097454966610752991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4209462372852977181365237 394637097454966610752991)
                    ·
                      rfl

theorem cell23_2305659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 5].length) (baseStart_2305659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305659 prefixEnd_2305659 := by exact prefixLift 2305659
  have htrace : WordTrace (prefixWord ++ tailWord_2305659) baseStart_2305659 baseEnd_2305659 := by
    simpa [prefixWord, tailWord_2305659, baseEnd_2305659] using wordTrace_append hprefix tailTrace_2305659
  have hstable : (prefixWord ++ tailWord_2305659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305659).length < 2 ^ (prefixWord ++ tailWord_2305659).sum := by decide
  have hdescent : baseEnd_2305659 < baseStart_2305659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305734 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2305734 : Nat := 118140960795 + 2305734 * 2 ^ 59
def prefixEnd_2305734 : Nat := 4983230072969 + 3 ^ 40 * 2305734 * 2
def baseEnd_2305734 : Nat := 1183949803413987038821129

theorem tailTrace_2305734 : CollatzResearch.WordTrace tailWord_2305734 prefixEnd_2305734 1183949803413987038821129 := by
  unfold tailWord_2305734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2628032119647718151913883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56064685219151320574162837 2628032119647718151913883)
  ·
    refine ⟨3942048179471577227870825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2628032119647718151913883 3942048179471577227870825)
    ·
      refine ⟨2956536134603682920903119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3942048179471577227870825 2956536134603682920903119)
      ·
        refine ⟨4434804201905524381354679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2956536134603682920903119 4434804201905524381354679)
        ·
          refine ⟨6652206302858286572032019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4434804201905524381354679 6652206302858286572032019)
          ·
            refine ⟨9978309454287429858048029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6652206302858286572032019 9978309454287429858048029)
            ·
              refine ⟨3741866045357786196768011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9978309454287429858048029 3741866045357786196768011)
              ·
                refine ⟨5612799068036679295152017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741866045357786196768011 5612799068036679295152017)
                ·
                  refine ⟨4209599301027509471364013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5612799068036679295152017 4209599301027509471364013)
                  ·
                    refine ⟨1578599737885316051761505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4209599301027509471364013 1578599737885316051761505)
                    ·
                      refine ⟨1183949803413987038821129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578599737885316051761505 1183949803413987038821129)
                      ·
                        rfl

theorem cell23_2305734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2305734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305734 prefixEnd_2305734 := by exact prefixLift 2305734
  have htrace : WordTrace (prefixWord ++ tailWord_2305734) baseStart_2305734 baseEnd_2305734 := by
    simpa [prefixWord, tailWord_2305734, baseEnd_2305734] using wordTrace_append hprefix tailTrace_2305734
  have hstable : (prefixWord ++ tailWord_2305734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305734).length < 2 ^ (prefixWord ++ tailWord_2305734).sum := by decide
  have hdescent : baseEnd_2305734 < baseStart_2305734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305736 : List Nat := [2, 1, 3, 1, 2, 2, 5, 7]
def baseStart_2305736 : Nat := 118140960795 + 2305736 * 2 ^ 59
def prefixEnd_2305736 : Nat := 4983230072969 + 3 ^ 40 * 2305736 * 2
def baseEnd_2305736 : Nat := 43850030754640593740597

theorem tailTrace_2305736 : CollatzResearch.WordTrace tailWord_2305736 prefixEnd_2305736 43850030754640593740597 := by
  unfold tailWord_2305736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42048550387359867601408531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56064733849813156801878041 42048550387359867601408531)
  ·
    refine ⟨63072825581039801402112797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42048550387359867601408531 63072825581039801402112797)
    ·
      refine ⟨23652309592889925525792299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63072825581039801402112797 23652309592889925525792299)
      ·
        refine ⟨35478464389334888288688449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23652309592889925525792299 35478464389334888288688449)
        ·
          refine ⟨26608848292001166216516337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35478464389334888288688449 26608848292001166216516337)
          ·
            refine ⟨19956636219000874662387253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26608848292001166216516337 19956636219000874662387253)
            ·
              refine ⟨1870934645531331999598805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19956636219000874662387253 1870934645531331999598805)
              ·
                refine ⟨43850030754640593740597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1870934645531331999598805 43850030754640593740597)
                ·
                  rfl

theorem cell23_2305736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 7].length) (baseStart_2305736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305736 prefixEnd_2305736 := by exact prefixLift 2305736
  have htrace : WordTrace (prefixWord ++ tailWord_2305736) baseStart_2305736 baseEnd_2305736 := by
    simpa [prefixWord, tailWord_2305736, baseEnd_2305736] using wordTrace_append hprefix tailTrace_2305736
  have hstable : (prefixWord ++ tailWord_2305736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305736).length < 2 ^ (prefixWord ++ tailWord_2305736).sum := by decide
  have hdescent : baseEnd_2305736 < baseStart_2305736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305803 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 1, 4, 2]
def baseStart_2305803 : Nat := 118140960795 + 2305803 * 2 ^ 59
def prefixEnd_2305803 : Nat := 4983230072969 + 3 ^ 40 * 2305803 * 2
def baseEnd_2305803 : Nat := 1183985233579147268858311

theorem tailTrace_2305803 : CollatzResearch.WordTrace tailWord_2305803 prefixEnd_2305803 1183985233579147268858311 := by
  unfold tailWord_2305803
  simp only [CollatzResearch.WordTrace]
  refine ⟨84099544465477005645506063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56066362976984670430337375 84099544465477005645506063)
  ·
    refine ⟨126149316698215508468259095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84099544465477005645506063 126149316698215508468259095)
    ·
      refine ⟨189223975047323262702388643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126149316698215508468259095 189223975047323262702388643)
      ·
        refine ⟨283835962570984894053582965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189223975047323262702388643 283835962570984894053582965)
        ·
          refine ⟨26609621491029833817523403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 283835962570984894053582965 26609621491029833817523403)
          ·
            refine ⟨39914432236544750726285105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26609621491029833817523403 39914432236544750726285105)
            ·
              refine ⟨29935824177408563044713829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39914432236544750726285105 29935824177408563044713829)
              ·
                refine ⟨5612967033264105570883843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29935824177408563044713829 5612967033264105570883843)
                ·
                  refine ⟨8419450549896158356325765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5612967033264105570883843 8419450549896158356325765)
                  ·
                    refine ⟨1578646978105529691811081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8419450549896158356325765 1578646978105529691811081)
                    ·
                      refine ⟨1183985233579147268858311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578646978105529691811081 1183985233579147268858311)
                      ·
                        rfl

theorem cell23_2305803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 4, 2].length) (baseStart_2305803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305803 prefixEnd_2305803 := by exact prefixLift 2305803
  have htrace : WordTrace (prefixWord ++ tailWord_2305803) baseStart_2305803 baseEnd_2305803 := by
    simpa [prefixWord, tailWord_2305803, baseEnd_2305803] using wordTrace_append hprefix tailTrace_2305803
  have hstable : (prefixWord ++ tailWord_2305803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305803).length < 2 ^ (prefixWord ++ tailWord_2305803).sum := by decide
  have hdescent : baseEnd_2305803 < baseStart_2305803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305806 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2305806 : Nat := 118140960795 + 2305806 * 2 ^ 59
def prefixEnd_2305806 : Nat := 4983230072969 + 3 ^ 40 * 2305806 * 2
def baseEnd_2305806 : Nat := 1183986774021110757120797

theorem tailTrace_2305806 : CollatzResearch.WordTrace tailWord_2305806 prefixEnd_2305806 1183986774021110757120797 := by
  unfold tailWord_2305806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10512456735558267144733159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56066435922977424771910181 10512456735558267144733159)
  ·
    refine ⟨15768685103337400717099739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10512456735558267144733159 15768685103337400717099739)
    ·
      refine ⟨23653027655006101075649609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15768685103337400717099739 23653027655006101075649609)
      ·
        refine ⟨17739770741254575806737207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23653027655006101075649609 17739770741254575806737207)
        ·
          refine ⟨26609656111881863710105811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17739770741254575806737207 26609656111881863710105811)
          ·
            refine ⟨39914484167822795565158717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26609656111881863710105811 39914484167822795565158717)
            ·
              refine ⟨14967931562933548336934519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39914484167822795565158717 14967931562933548336934519)
              ·
                refine ⟨22451897344400322505401779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14967931562933548336934519 22451897344400322505401779)
                ·
                  refine ⟨33677846016600483758102669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22451897344400322505401779 33677846016600483758102669)
                  ·
                    refine ⟨12629192256225181409288501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33677846016600483758102669 12629192256225181409288501)
                    ·
                      refine ⟨1183986774021110757120797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12629192256225181409288501 1183986774021110757120797)
                      ·
                        rfl

theorem cell23_2305806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2305806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305806 prefixEnd_2305806 := by exact prefixLift 2305806
  have htrace : WordTrace (prefixWord ++ tailWord_2305806) baseStart_2305806 baseEnd_2305806 := by
    simpa [prefixWord, tailWord_2305806, baseEnd_2305806] using wordTrace_append hprefix tailTrace_2305806
  have hstable : (prefixWord ++ tailWord_2305806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305806).length < 2 ^ (prefixWord ++ tailWord_2305806).sum := by decide
  have hdescent : baseEnd_2305806 < baseStart_2305806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305816 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2305816 : Nat := 118140960795 + 2305816 * 2 ^ 59
def prefixEnd_2305816 : Nat := 4983230072969 + 3 ^ 40 * 2305816 * 2
def baseEnd_2305816 : Nat := 1183991908827655717995751

theorem tailTrace_2305816 : CollatzResearch.WordTrace tailWord_2305816 prefixEnd_2305816 1183991908827655717995751 := by
  unfold tailWord_2305816
  simp only [CollatzResearch.WordTrace]
  refine ⟨42050009307214954432864651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56066679076286605910486201 42050009307214954432864651)
  ·
    refine ⟨63075013960822431649296977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42050009307214954432864651 63075013960822431649296977)
    ·
      refine ⟨47306260470616823736972733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63075013960822431649296977 47306260470616823736972733)
      ·
        refine ⟨17739847676481308901364775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47306260470616823736972733 17739847676481308901364775)
        ·
          refine ⟨26609771514721963352047163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17739847676481308901364775 26609771514721963352047163)
          ·
            refine ⟨39914657272082945028070745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26609771514721963352047163 39914657272082945028070745)
            ·
              refine ⟨29935992954062208771053059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39914657272082945028070745 29935992954062208771053059)
              ·
                refine ⟨44903989431093313156579589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29935992954062208771053059 44903989431093313156579589)
                ·
                  refine ⟨8419498018329996216858673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44903989431093313156579589 8419498018329996216858673)
                  ·
                    refine ⟨6314623513747497162644005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8419498018329996216858673 6314623513747497162644005)
                    ·
                      refine ⟨1183991908827655717995751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6314623513747497162644005 1183991908827655717995751)
                      ·
                        rfl

theorem cell23_2305816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2305816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305816 prefixEnd_2305816 := by exact prefixLift 2305816
  have htrace : WordTrace (prefixWord ++ tailWord_2305816) baseStart_2305816 baseEnd_2305816 := by
    simpa [prefixWord, tailWord_2305816, baseEnd_2305816] using wordTrace_append hprefix tailTrace_2305816
  have hstable : (prefixWord ++ tailWord_2305816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305816).length < 2 ^ (prefixWord ++ tailWord_2305816).sum := by decide
  have hdescent : baseEnd_2305816 < baseStart_2305816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305820 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_2305820 : Nat := 118140960795 + 2305820 * 2 ^ 59
def prefixEnd_2305820 : Nat := 4983230072969 + 3 ^ 40 * 2305820 * 2
def baseEnd_2305820 : Nat := 1183993962750273702345733

theorem tailTrace_2305820 : CollatzResearch.WordTrace tailWord_2305820 prefixEnd_2305820 1183993962750273702345733 := by
  unfold tailWord_2305820
  simp only [CollatzResearch.WordTrace]
  refine ⟨42050082253207708774437457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56066776337610278365916609 42050082253207708774437457)
  ·
    refine ⟨31537561689905781580828093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42050082253207708774437457 31537561689905781580828093)
    ·
      refine ⟨11826585633714668092810535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31537561689905781580828093 11826585633714668092810535)
      ·
        refine ⟨17739878450572002139215803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11826585633714668092810535 17739878450572002139215803)
        ·
          refine ⟨26609817675858003208823705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17739878450572002139215803 26609817675858003208823705)
          ·
            refine ⟨19957363256893502406617779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26609817675858003208823705 19957363256893502406617779)
            ·
              refine ⟨29936044885340253609926669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19957363256893502406617779 29936044885340253609926669)
              ·
                refine ⟨11226016832002595103722501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29936044885340253609926669 11226016832002595103722501)
                ·
                  refine ⟨2104878156000486581947969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11226016832002595103722501 2104878156000486581947969)
                  ·
                    refine ⟨1578658617000364936460977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2104878156000486581947969 1578658617000364936460977)
                    ·
                      refine ⟨1183993962750273702345733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578658617000364936460977 1183993962750273702345733)
                      ·
                        rfl

theorem cell23_2305820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_2305820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305820 prefixEnd_2305820 := by exact prefixLift 2305820
  have htrace : WordTrace (prefixWord ++ tailWord_2305820) baseStart_2305820 baseEnd_2305820 := by
    simpa [prefixWord, tailWord_2305820, baseEnd_2305820] using wordTrace_append hprefix tailTrace_2305820
  have hstable : (prefixWord ++ tailWord_2305820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305820).length < 2 ^ (prefixWord ++ tailWord_2305820).sum := by decide
  have hdescent : baseEnd_2305820 < baseStart_2305820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305866 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_2305866 : Nat := 118140960795 + 2305866 * 2 ^ 59
def prefixEnd_2305866 : Nat := 4983230072969 + 3 ^ 40 * 2305866 * 2
def baseEnd_2305866 : Nat := 1184017582860380522370521

theorem tailTrace_2305866 : CollatzResearch.WordTrace tailWord_2305866 prefixEnd_2305866 1184017582860380522370521 := by
  unfold tailWord_2305866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21025460566062191851262363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56067894842832511603366301 21025460566062191851262363)
  ·
    refine ⟨31538190849093287776893545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21025460566062191851262363 31538190849093287776893545)
    ·
      refine ⟨23653643136819965832670159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31538190849093287776893545 23653643136819965832670159)
      ·
        refine ⟨35480464705229948749005239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23653643136819965832670159 35480464705229948749005239)
        ·
          refine ⟨53220697057844923123507859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35480464705229948749005239 53220697057844923123507859)
          ·
            refine ⟨79831045586767384685261789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53220697057844923123507859 79831045586767384685261789)
            ·
              refine ⟨29936642095037769256973171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79831045586767384685261789 29936642095037769256973171)
              ·
                refine ⟨44904963142556653885459757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29936642095037769256973171 44904963142556653885459757)
                ·
                  refine ⟨16839361178458745207047409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44904963142556653885459757 16839361178458745207047409)
                  ·
                    refine ⟨12629520883844058905285557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16839361178458745207047409 12629520883844058905285557)
                    ·
                      refine ⟨1184017582860380522370521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12629520883844058905285557 1184017582860380522370521)
                      ·
                        rfl

theorem cell23_2305866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_2305866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305866 prefixEnd_2305866 := by exact prefixLift 2305866
  have htrace : WordTrace (prefixWord ++ tailWord_2305866) baseStart_2305866 baseEnd_2305866 := by
    simpa [prefixWord, tailWord_2305866, baseEnd_2305866] using wordTrace_append hprefix tailTrace_2305866
  have hstable : (prefixWord ++ tailWord_2305866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305866).length < 2 ^ (prefixWord ++ tailWord_2305866).sum := by decide
  have hdescent : baseEnd_2305866 < baseStart_2305866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305873 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 2, 5]
def baseStart_2305873 : Nat := 118140960795 + 2305873 * 2 ^ 59
def prefixEnd_2305873 : Nat := 4983230072969 + 3 ^ 40 * 2305873 * 2
def baseEnd_2305873 : Nat := 394673725741653998327663

theorem tailTrace_2305873 : CollatzResearch.WordTrace tailWord_2305873 prefixEnd_2305873 394673725741653998327663 := by
  unfold tailWord_2305873
  simp only [CollatzResearch.WordTrace]
  refine ⟨84102097575223407600554273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56068065050148938400369515 84102097575223407600554273)
  ·
    refine ⟨63076573181417555700415705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84102097575223407600554273 63076573181417555700415705)
    ·
      refine ⟨47307429886063166775311779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63076573181417555700415705 47307429886063166775311779)
      ·
        refine ⟨70961144829094750162967669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47307429886063166775311779 70961144829094750162967669)
        ·
          refine ⟨6652607327727632827778219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70961144829094750162967669 6652607327727632827778219)
          ·
            refine ⟨9978910991591449241667329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6652607327727632827778219 9978910991591449241667329)
            ·
              refine ⟨7484183243693586931250497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9978910991591449241667329 7484183243693586931250497)
              ·
                refine ⟨5613137432770190198437873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7484183243693586931250497 5613137432770190198437873)
                ·
                  refine ⟨4209853074577642648828405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5613137432770190198437873 4209853074577642648828405)
                  ·
                    refine ⟨394673725741653998327663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4209853074577642648828405 394673725741653998327663)
                    ·
                      rfl

theorem cell23_2305873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_2305873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305873 prefixEnd_2305873 := by exact prefixLift 2305873
  have htrace : WordTrace (prefixWord ++ tailWord_2305873) baseStart_2305873 baseEnd_2305873 := by
    simpa [prefixWord, tailWord_2305873, baseEnd_2305873] using wordTrace_append hprefix tailTrace_2305873
  have hstable : (prefixWord ++ tailWord_2305873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305873).length < 2 ^ (prefixWord ++ tailWord_2305873).sum := by decide
  have hdescent : baseEnd_2305873 < baseStart_2305873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305877 : List Nat := [1, 3, 2, 2, 2, 4, 2, 2, 5]
def baseStart_2305877 : Nat := 118140960795 + 2305877 * 2 ^ 59
def prefixEnd_2305877 : Nat := 4983230072969 + 3 ^ 40 * 2305877 * 2
def baseEnd_2305877 : Nat := 131558136794175553259219

theorem tailTrace_2305877 : CollatzResearch.WordTrace tailWord_2305877 prefixEnd_2305877 131558136794175553259219 := by
  unfold tailWord_2305877
  simp only [CollatzResearch.WordTrace]
  refine ⟨84102243467208916283699885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56068162311472610855799923 84102243467208916283699885)
  ·
    refine ⟨31538341300203343606387457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84102243467208916283699885 31538341300203343606387457)
    ·
      refine ⟨23653755975152507704790593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31538341300203343606387457 23653755975152507704790593)
      ·
        refine ⟨17740316981364380778592945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23653755975152507704790593 17740316981364380778592945)
        ·
          refine ⟨13305237736023285583944709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17740316981364380778592945 13305237736023285583944709)
          ·
            refine ⟨2494732075504366046989633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13305237736023285583944709 2494732075504366046989633)
            ·
              refine ⟨1871049056628274535242225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2494732075504366046989633 1871049056628274535242225)
              ·
                refine ⟨1403286792471205901431669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871049056628274535242225 1403286792471205901431669)
                ·
                  refine ⟨131558136794175553259219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1403286792471205901431669 131558136794175553259219)
                  ·
                    rfl

theorem cell23_2305877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_2305877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305877 prefixEnd_2305877 := by exact prefixLift 2305877
  have htrace : WordTrace (prefixWord ++ tailWord_2305877) baseStart_2305877 baseEnd_2305877 := by
    simpa [prefixWord, tailWord_2305877, baseEnd_2305877] using wordTrace_append hprefix tailTrace_2305877
  have hstable : (prefixWord ++ tailWord_2305877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305877).length < 2 ^ (prefixWord ++ tailWord_2305877).sum := by decide
  have hdescent : baseEnd_2305877 < baseStart_2305877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305913 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 3]
def baseStart_2305913 : Nat := 118140960795 + 2305913 * 2 ^ 59
def prefixEnd_2305913 : Nat := 4983230072969 + 3 ^ 40 * 2305913 * 2
def baseEnd_2305913 : Nat := 1184041716451141838482805

theorem tailTrace_2305913 : CollatzResearch.WordTrace tailWord_2305913 prefixEnd_2305913 1184041716451141838482805 := by
  unfold tailWord_2305913
  simp only [CollatzResearch.WordTrace]
  refine ⟨84103556495078494432010393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56069037663385662954673595 84103556495078494432010393)
  ·
    refine ⟨63077667371308870824007795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84103556495078494432010393 63077667371308870824007795)
    ·
      refine ⟨94616501056963306236011693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63077667371308870824007795 94616501056963306236011693)
      ·
        refine ⟨35481187896361239838504385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94616501056963306236011693 35481187896361239838504385)
        ·
          refine ⟨26610890922270929878878289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35481187896361239838504385 26610890922270929878878289)
          ·
            refine ⟨19958168191703197409158717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26610890922270929878878289 19958168191703197409158717)
            ·
              refine ⟨7484313071888699028434519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19958168191703197409158717 7484313071888699028434519)
              ·
                refine ⟨11226469607833048542651779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7484313071888699028434519 11226469607833048542651779)
                ·
                  refine ⟨16839704411749572813977669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11226469607833048542651779 16839704411749572813977669)
                  ·
                    refine ⟨3157444577203044902620813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16839704411749572813977669 3157444577203044902620813)
                    ·
                      refine ⟨1184041716451141838482805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3157444577203044902620813 1184041716451141838482805)
                      ·
                        rfl

theorem cell23_2305913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_2305913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305913 prefixEnd_2305913 := by exact prefixLift 2305913
  have htrace : WordTrace (prefixWord ++ tailWord_2305913) baseStart_2305913 baseEnd_2305913 := by
    simpa [prefixWord, tailWord_2305913, baseEnd_2305913] using wordTrace_append hprefix tailTrace_2305913
  have hstable : (prefixWord ++ tailWord_2305913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305913).length < 2 ^ (prefixWord ++ tailWord_2305913).sum := by decide
  have hdescent : baseEnd_2305913 < baseStart_2305913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305936 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_2305936 : Nat := 118140960795 + 2305936 * 2 ^ 59
def prefixEnd_2305936 : Nat := 4983230072969 + 3 ^ 40 * 2305936 * 2
def baseEnd_2305936 : Nat := 1184053526506195248495199

theorem tailTrace_2305936 : CollatzResearch.WordTrace tailWord_2305936 prefixEnd_2305936 1184053526506195248495199 := by
  unfold tailWord_2305936
  simp only [CollatzResearch.WordTrace]
  refine ⟨42052197686997584680048831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56069596915996779573398441 42052197686997584680048831)
  ·
    refine ⟨63078296530496377020073247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42052197686997584680048831 63078296530496377020073247)
    ·
      refine ⟨94617444795744565530109871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63078296530496377020073247 94617444795744565530109871)
      ·
        refine ⟨141926167193616848295164807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94617444795744565530109871 141926167193616848295164807)
        ·
          refine ⟨212889250790425272442747211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141926167193616848295164807 212889250790425272442747211)
          ·
            refine ⟨319333876185637908664120817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212889250790425272442747211 319333876185637908664120817)
            ·
              refine ⟨239500407139228431498090613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319333876185637908664120817 239500407139228431498090613)
              ·
                refine ⟨22453163169302665452945995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239500407139228431498090613 22453163169302665452945995)
                ·
                  refine ⟨33679744753953998179418993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22453163169302665452945995 33679744753953998179418993)
                  ·
                    refine ⟨25259808565465498634564245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33679744753953998179418993 25259808565465498634564245)
                    ·
                      refine ⟨1184053526506195248495199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25259808565465498634564245 1184053526506195248495199)
                      ·
                        rfl

theorem cell23_2305936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_2305936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305936 prefixEnd_2305936 := by exact prefixLift 2305936
  have htrace : WordTrace (prefixWord ++ tailWord_2305936) baseStart_2305936 baseEnd_2305936 := by
    simpa [prefixWord, tailWord_2305936, baseEnd_2305936] using wordTrace_append hprefix tailTrace_2305936
  have hstable : (prefixWord ++ tailWord_2305936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305936).length < 2 ^ (prefixWord ++ tailWord_2305936).sum := by decide
  have hdescent : baseEnd_2305936 < baseStart_2305936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305970 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_2305970 : Nat := 118140960795 + 2305970 * 2 ^ 59
def prefixEnd_2305970 : Nat := 4983230072969 + 3 ^ 40 * 2305970 * 2
def baseEnd_2305970 : Nat := 1184070984848448115470043

theorem tailTrace_2305970 : CollatzResearch.WordTrace tailWord_2305970 prefixEnd_2305970 1184070984848448115470043 := by
  unfold tailWord_2305970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21026408863967998291708841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56070423637247995444556909 21026408863967998291708841)
  ·
    refine ⟨15769806647975998718781631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21026408863967998291708841 15769806647975998718781631)
    ·
      refine ⟨23654709971963998078172447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15769806647975998718781631 23654709971963998078172447)
      ·
        refine ⟨35482064957945997117258671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23654709971963998078172447 35482064957945997117258671)
        ·
          refine ⟨53223097436918995675888007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35482064957945997117258671 53223097436918995675888007)
          ·
            refine ⟨79834646155378493513832011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53223097436918995675888007 79834646155378493513832011)
            ·
              refine ⟨119751969233067740270748017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79834646155378493513832011 119751969233067740270748017)
              ·
                refine ⟨89813976924800805203061013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119751969233067740270748017 89813976924800805203061013)
                ·
                  refine ⟨4210030168350037743893485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89813976924800805203061013 4210030168350037743893485)
                  ·
                    refine ⟨1578761313131264153960057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4210030168350037743893485 1578761313131264153960057)
                    ·
                      refine ⟨1184070984848448115470043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578761313131264153960057 1184070984848448115470043)
                      ·
                        rfl

theorem cell23_2305970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_2305970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2305970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2305970 prefixEnd_2305970 := by exact prefixLift 2305970
  have htrace : WordTrace (prefixWord ++ tailWord_2305970) baseStart_2305970 baseEnd_2305970 := by
    simpa [prefixWord, tailWord_2305970, baseEnd_2305970] using wordTrace_append hprefix tailTrace_2305970
  have hstable : (prefixWord ++ tailWord_2305970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305970).length < 2 ^ (prefixWord ++ tailWord_2305970).sum := by decide
  have hdescent : baseEnd_2305970 < baseStart_2305970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306017 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_2306017 : Nat := 118140960795 + 2306017 * 2 ^ 59
def prefixEnd_2306017 : Nat := 4983230072969 + 3 ^ 40 * 2306017 * 2
def baseEnd_2306017 : Nat := 1184095118439209431582327

theorem tailTrace_2306017 : CollatzResearch.WordTrace tailWord_2306017 prefixEnd_2306017 1184095118439209431582327 := by
  unfold tailWord_2306017
  simp only [CollatzResearch.WordTrace]
  refine ⟨84107349686701720193796305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56071566457801146795864203 84107349686701720193796305)
  ·
    refine ⟨63080512265026290145347229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84107349686701720193796305 63080512265026290145347229)
    ·
      refine ⟨23655192099384858804505211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63080512265026290145347229 23655192099384858804505211)
      ·
        refine ⟨35482788149077288206757817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23655192099384858804505211 35482788149077288206757817)
        ·
          refine ⟨26612091111807966155068363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35482788149077288206757817 26612091111807966155068363)
          ·
            refine ⟨39918136667711949232602545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26612091111807966155068363 39918136667711949232602545)
            ·
              refine ⟨29938602500783961924451909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39918136667711949232602545 29938602500783961924451909)
              ·
                refine ⟨5613487968896992860834733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29938602500783961924451909 5613487968896992860834733)
                ·
                  refine ⟨2105057988336372322813025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5613487968896992860834733 2105057988336372322813025)
                  ·
                    refine ⟨1578793491252279242109769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105057988336372322813025 1578793491252279242109769)
                    ·
                      refine ⟨1184095118439209431582327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578793491252279242109769 1184095118439209431582327)
                      ·
                        rfl

theorem cell23_2306017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_2306017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306017 prefixEnd_2306017 := by exact prefixLift 2306017
  have htrace : WordTrace (prefixWord ++ tailWord_2306017) baseStart_2306017 baseEnd_2306017 := by
    simpa [prefixWord, tailWord_2306017, baseEnd_2306017] using wordTrace_append hprefix tailTrace_2306017
  have hstable : (prefixWord ++ tailWord_2306017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306017).length < 2 ^ (prefixWord ++ tailWord_2306017).sum := by decide
  have hdescent : baseEnd_2306017 < baseStart_2306017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306020 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_2306020 : Nat := 118140960795 + 2306020 * 2 ^ 59
def prefixEnd_2306020 : Nat := 4983230072969 + 3 ^ 40 * 2306020 * 2
def baseEnd_2306020 : Nat := 1184096658881172919844813

theorem tailTrace_2306020 : CollatzResearch.WordTrace tailWord_2306020 prefixEnd_2306020 1184096658881172919844813 := by
  unfold tailWord_2306020
  simp only [CollatzResearch.WordTrace]
  refine ⟨42053729552845425853077757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56071639403793901137437009 42053729552845425853077757)
  ·
    refine ⟨15770148582317034694904159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42053729552845425853077757 15770148582317034694904159)
    ·
      refine ⟨23655222873475552042356239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15770148582317034694904159 23655222873475552042356239)
      ·
        refine ⟨35482834310213328063534359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23655222873475552042356239 35482834310213328063534359)
        ·
          refine ⟨53224251465319992095301539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35482834310213328063534359 53224251465319992095301539)
          ·
            refine ⟨79836377197979988142952309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53224251465319992095301539 79836377197979988142952309)
            ·
              refine ⟨7484660362310623888401779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79836377197979988142952309 7484660362310623888401779)
              ·
                refine ⟨11226990543465935832602669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7484660362310623888401779 11226990543465935832602669)
                ·
                  refine ⟨4210121453799725937226001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11226990543465935832602669 4210121453799725937226001)
                  ·
                    refine ⟨3157591090349794452919501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4210121453799725937226001 3157591090349794452919501)
                    ·
                      refine ⟨1184096658881172919844813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3157591090349794452919501 1184096658881172919844813)
                      ·
                        rfl

theorem cell23_2306020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_2306020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306020 prefixEnd_2306020 := by exact prefixLift 2306020
  have htrace : WordTrace (prefixWord ++ tailWord_2306020) baseStart_2306020 baseEnd_2306020 := by
    simpa [prefixWord, tailWord_2306020, baseEnd_2306020] using wordTrace_append hprefix tailTrace_2306020
  have hstable : (prefixWord ++ tailWord_2306020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306020).length < 2 ^ (prefixWord ++ tailWord_2306020).sum := by decide
  have hdescent : baseEnd_2306020 < baseStart_2306020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306030 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2306030 : Nat := 118140960795 + 2306030 * 2 ^ 59
def prefixEnd_2306030 : Nat := 4983230072969 + 3 ^ 40 * 2306030 * 2
def baseEnd_2306030 : Nat := 1184101793687717880719767

theorem tailTrace_2306030 : CollatzResearch.WordTrace tailWord_2306030 prefixEnd_2306030 1184101793687717880719767 := by
  unfold tailWord_2306030
  simp only [CollatzResearch.WordTrace]
  refine ⟨10513477979456827926752443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56071882557103082276013029 10513477979456827926752443)
  ·
    refine ⟨15770216969185241890128665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10513477979456827926752443 15770216969185241890128665)
    ·
      refine ⟨11827662726888931417596499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15770216969185241890128665 11827662726888931417596499)
      ·
        refine ⟨17741494090333397126394749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11827662726888931417596499 17741494090333397126394749)
        ·
          refine ⟨6653060283875023922398031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17741494090333397126394749 6653060283875023922398031)
          ·
            refine ⟨9979590425812535883597047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653060283875023922398031 9979590425812535883597047)
            ·
              refine ⟨14969385638718803825395571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9979590425812535883597047 14969385638718803825395571)
              ·
                refine ⟨22454078458078205738093357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14969385638718803825395571 22454078458078205738093357)
                ·
                  refine ⟨8420279421779327151785009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22454078458078205738093357 8420279421779327151785009)
                  ·
                    refine ⟨6315209566334495363838757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8420279421779327151785009 6315209566334495363838757)
                    ·
                      refine ⟨1184101793687717880719767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6315209566334495363838757 1184101793687717880719767)
                      ·
                        rfl

theorem cell23_2306030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2306030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306030 prefixEnd_2306030 := by exact prefixLift 2306030
  have htrace : WordTrace (prefixWord ++ tailWord_2306030) baseStart_2306030 baseEnd_2306030 := by
    simpa [prefixWord, tailWord_2306030, baseEnd_2306030] using wordTrace_append hprefix tailTrace_2306030
  have hstable : (prefixWord ++ tailWord_2306030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306030).length < 2 ^ (prefixWord ++ tailWord_2306030).sum := by decide
  have hdescent : baseEnd_2306030 < baseStart_2306030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306053 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_2306053 : Nat := 118140960795 + 2306053 * 2 ^ 59
def prefixEnd_2306053 : Nat := 4983230072969 + 3 ^ 40 * 2306053 * 2
def baseEnd_2306053 : Nat := 394704534580923763577387

theorem tailTrace_2306053 : CollatzResearch.WordTrace tailWord_2306053 prefixEnd_2306053 394704534580923763577387 := by
  unfold tailWord_2306053
  simp only [CollatzResearch.WordTrace]
  refine ⟨84108662714571298342106813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56072441809714198894737875 84108662714571298342106813)
  ·
    refine ⟨31540748517964236878290055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84108662714571298342106813 31540748517964236878290055)
    ·
      refine ⟨47311122776946355317435083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31540748517964236878290055 47311122776946355317435083)
      ·
        refine ⟨70966684165419532976152625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47311122776946355317435083 70966684165419532976152625)
        ·
          refine ⟨53225013124064649732114469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70966684165419532976152625 53225013124064649732114469)
          ·
            refine ⟨9979689960762121824771463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53225013124064649732114469 9979689960762121824771463)
            ·
              refine ⟨14969534941143182737157195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9979689960762121824771463 14969534941143182737157195)
              ·
                refine ⟨22454302411714774105735793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14969534941143182737157195 22454302411714774105735793)
                ·
                  refine ⟨16840726808786080579301845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22454302411714774105735793 16840726808786080579301845)
                  ·
                    refine ⟨394704534580923763577387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16840726808786080579301845 394704534580923763577387)
                    ·
                      rfl

theorem cell23_2306053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_2306053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306053 prefixEnd_2306053 := by exact prefixLift 2306053
  have htrace : WordTrace (prefixWord ++ tailWord_2306053) baseStart_2306053 baseEnd_2306053 := by
    simpa [prefixWord, tailWord_2306053, baseEnd_2306053] using wordTrace_append hprefix tailTrace_2306053
  have hstable : (prefixWord ++ tailWord_2306053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306053).length < 2 ^ (prefixWord ++ tailWord_2306053).sum := by decide
  have hdescent : baseEnd_2306053 < baseStart_2306053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306061 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2306061 : Nat := 118140960795 + 2306061 * 2 ^ 59
def prefixEnd_2306061 : Nat := 4983230072969 + 3 ^ 40 * 2306061 * 2
def baseEnd_2306061 : Nat := 394705903862669086477375

theorem tailTrace_2306061 : CollatzResearch.WordTrace tailWord_2306061 prefixEnd_2306061 394705903862669086477375 := by
  unfold tailWord_2306061
  simp only [CollatzResearch.WordTrace]
  refine ⟨84108954498542315708398037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56072636332361543805598691 84108954498542315708398037)
  ·
    refine ⟨1971303621059585524415579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 84108954498542315708398037 1971303621059585524415579)
    ·
      refine ⟨2956955431589378286623369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971303621059585524415579 2956955431589378286623369)
      ·
        refine ⟨2217716573692033714967527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2956955431589378286623369 2217716573692033714967527)
        ·
          refine ⟨3326574860538050572451291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217716573692033714967527 3326574860538050572451291)
          ·
            refine ⟨4989862290807075858676937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326574860538050572451291 4989862290807075858676937)
            ·
              refine ⟨3742396718105306894007703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4989862290807075858676937 3742396718105306894007703)
              ·
                refine ⟨5613595077157960341011555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742396718105306894007703 5613595077157960341011555)
                ·
                  refine ⟨8420392615736940511517333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613595077157960341011555 8420392615736940511517333)
                  ·
                    refine ⟨394705903862669086477375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8420392615736940511517333 394705903862669086477375)
                    ·
                      rfl

theorem cell23_2306061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2306061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306061 prefixEnd_2306061 := by exact prefixLift 2306061
  have htrace : WordTrace (prefixWord ++ tailWord_2306061) baseStart_2306061 baseEnd_2306061 := by
    simpa [prefixWord, tailWord_2306061, baseEnd_2306061] using wordTrace_append hprefix tailTrace_2306061
  have hstable : (prefixWord ++ tailWord_2306061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306061).length < 2 ^ (prefixWord ++ tailWord_2306061).sum := by decide
  have hdescent : baseEnd_2306061 < baseStart_2306061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306067 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 3]
def baseStart_2306067 : Nat := 118140960795 + 2306067 * 2 ^ 59
def prefixEnd_2306067 : Nat := 4983230072969 + 3 ^ 40 * 2306067 * 2
def baseEnd_2306067 : Nat := 1184120792471934235957097

theorem tailTrace_2306067 : CollatzResearch.WordTrace tailWord_2306067 prefixEnd_2306067 1184120792471934235957097 := by
  unfold tailWord_2306067
  simp only [CollatzResearch.WordTrace]
  refine ⟨84109173336520578733116455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56072782224347052488744303 84109173336520578733116455)
  ·
    refine ⟨126163760004780868099674683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84109173336520578733116455 126163760004780868099674683)
    ·
      refine ⟨189245640007171302149512025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126163760004780868099674683 189245640007171302149512025)
      ·
        refine ⟨141934230005378476612134019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189245640007171302149512025 141934230005378476612134019)
        ·
          refine ⟨212901345008067714918201029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141934230005378476612134019 212901345008067714918201029)
          ·
            refine ⟨39919002189012696547162693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212901345008067714918201029 39919002189012696547162693)
            ·
              refine ⟨7484812910439880602593005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39919002189012696547162693 7484812910439880602593005)
              ·
                refine ⟨2806804841414955225972377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7484812910439880602593005 2806804841414955225972377)
                ·
                  refine ⟨2105103631061216419479283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2806804841414955225972377 2105103631061216419479283)
                  ·
                    refine ⟨3157655446591824629218925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2105103631061216419479283 3157655446591824629218925)
                    ·
                      refine ⟨1184120792471934235957097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3157655446591824629218925 1184120792471934235957097)
                      ·
                        rfl

theorem cell23_2306067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 3].length) (baseStart_2306067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306067 prefixEnd_2306067 := by exact prefixLift 2306067
  have htrace : WordTrace (prefixWord ++ tailWord_2306067) baseStart_2306067 baseEnd_2306067 := by
    simpa [prefixWord, tailWord_2306067, baseEnd_2306067] using wordTrace_append hprefix tailTrace_2306067
  have hstable : (prefixWord ++ tailWord_2306067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306067).length < 2 ^ (prefixWord ++ tailWord_2306067).sum := by decide
  have hdescent : baseEnd_2306067 < baseStart_2306067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306068 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2306068 : Nat := 118140960795 + 2306068 * 2 ^ 59
def prefixEnd_2306068 : Nat := 4983230072969 + 3 ^ 40 * 2306068 * 2
def baseEnd_2306068 : Nat := 1184121305952588732044593

theorem tailTrace_2306068 : CollatzResearch.WordTrace tailWord_2306068 prefixEnd_2306068 1184121305952588732044593 := by
  unfold tailWord_2306068
  simp only [CollatzResearch.WordTrace]
  refine ⟨42054604904758477951951429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56072806539677970602601905 42054604904758477951951429)
  ·
    refine ⟨7885238419642214615990893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42054604904758477951951429 7885238419642214615990893)
    ·
      refine ⟨2956964407365830480996585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7885238419642214615990893 2956964407365830480996585)
      ·
        refine ⟨2217723305524372860747439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2956964407365830480996585 2217723305524372860747439)
        ·
          refine ⟨3326584958286559291121159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217723305524372860747439 3326584958286559291121159)
          ·
            refine ⟨4989877437429838936681739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326584958286559291121159 4989877437429838936681739)
            ·
              refine ⟨7484816156144758405022609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4989877437429838936681739 7484816156144758405022609)
              ·
                refine ⟨5613612117108568803766957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7484816156144758405022609 5613612117108568803766957)
                ·
                  refine ⟨2105104543915713301412609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5613612117108568803766957 2105104543915713301412609)
                  ·
                    refine ⟨1578828407936784976059457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105104543915713301412609 1578828407936784976059457)
                    ·
                      refine ⟨1184121305952588732044593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578828407936784976059457 1184121305952588732044593)
                      ·
                        rfl

theorem cell23_2306068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2306068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306068 prefixEnd_2306068 := by exact prefixLift 2306068
  have htrace : WordTrace (prefixWord ++ tailWord_2306068) baseStart_2306068 baseEnd_2306068 := by
    simpa [prefixWord, tailWord_2306068, baseEnd_2306068] using wordTrace_append hprefix tailTrace_2306068
  have hstable : (prefixWord ++ tailWord_2306068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306068).length < 2 ^ (prefixWord ++ tailWord_2306068).sum := by decide
  have hdescent : baseEnd_2306068 < baseStart_2306068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306073 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_2306073 : Nat := 118140960795 + 2306073 * 2 ^ 59
def prefixEnd_2306073 : Nat := 4983230072969 + 3 ^ 40 * 2306073 * 2
def baseEnd_2306073 : Nat := 1184123873355861212482069

theorem tailTrace_2306073 : CollatzResearch.WordTrace tailWord_2306073 prefixEnd_2306073 1184123873355861212482069 := by
  unfold tailWord_2306073
  simp only [CollatzResearch.WordTrace]
  refine ⟨84109392174498841757834873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56072928116332561171889915 84109392174498841757834873)
  ·
    refine ⟨63082044130874131318376155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84109392174498841757834873 63082044130874131318376155)
    ·
      refine ⟨94623066196311196977564233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63082044130874131318376155 94623066196311196977564233)
      ·
        refine ⟨70967299647233397733173175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94623066196311196977564233 70967299647233397733173175)
        ·
          refine ⟨106450949470850096599759763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70967299647233397733173175 106450949470850096599759763)
          ·
            refine ⟨159676424206275144899639645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106450949470850096599759763 159676424206275144899639645)
            ·
              refine ⟨59878659077353179337364867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159676424206275144899639645 59878659077353179337364867)
              ·
                refine ⟨89817988616029769006047301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59878659077353179337364867 89817988616029769006047301)
                ·
                  refine ⟨16840872865505581688633869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89817988616029769006047301 16840872865505581688633869)
                  ·
                    refine ⟨6315327324564593133237701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16840872865505581688633869 6315327324564593133237701)
                    ·
                      refine ⟨1184123873355861212482069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6315327324564593133237701 1184123873355861212482069)
                      ·
                        rfl

theorem cell23_2306073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_2306073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306073 prefixEnd_2306073 := by exact prefixLift 2306073
  have htrace : WordTrace (prefixWord ++ tailWord_2306073) baseStart_2306073 baseEnd_2306073 := by
    simpa [prefixWord, tailWord_2306073, baseEnd_2306073] using wordTrace_append hprefix tailTrace_2306073
  have hstable : (prefixWord ++ tailWord_2306073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306073).length < 2 ^ (prefixWord ++ tailWord_2306073).sum := by decide
  have hdescent : baseEnd_2306073 < baseStart_2306073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306083 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 1, 8]
def baseStart_2306083 : Nat := 118140960795 + 2306083 * 2 ^ 59
def prefixEnd_2306083 : Nat := 4983230072969 + 3 ^ 40 * 2306083 * 2
def baseEnd_2306083 : Nat := 394709669387468724452341

theorem tailTrace_2306083 : CollatzResearch.WordTrace tailWord_2306083 prefixEnd_2306083 394709669387468724452341 := by
  unfold tailWord_2306083
  simp only [CollatzResearch.WordTrace]
  refine ⟨84109756904462613465698903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56073171269641742310465935 84109756904462613465698903)
  ·
    refine ⟨126164635356693920198548355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84109756904462613465698903 126164635356693920198548355)
    ·
      refine ⟨189246953035040880297822533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126164635356693920198548355 189246953035040880297822533)
      ·
        refine ⟨35483803694070165055841725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189246953035040880297822533 35483803694070165055841725)
        ·
          refine ⟨13306426385276311895940647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35483803694070165055841725 13306426385276311895940647)
          ·
            refine ⟨19959639577914467843910971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13306426385276311895940647 19959639577914467843910971)
            ·
              refine ⟨29939459366871701765866457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19959639577914467843910971 29939459366871701765866457)
              ·
                refine ⟨22454594525153776324399843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29939459366871701765866457 22454594525153776324399843)
                ·
                  refine ⟨33681891787730664486599765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22454594525153776324399843 33681891787730664486599765)
                  ·
                    refine ⟨394709669387468724452341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33681891787730664486599765 394709669387468724452341)
                    ·
                      rfl

theorem cell23_2306083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 8].length) (baseStart_2306083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306083 prefixEnd_2306083 := by exact prefixLift 2306083
  have htrace : WordTrace (prefixWord ++ tailWord_2306083) baseStart_2306083 baseEnd_2306083 := by
    simpa [prefixWord, tailWord_2306083, baseEnd_2306083] using wordTrace_append hprefix tailTrace_2306083
  have hstable : (prefixWord ++ tailWord_2306083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306083).length < 2 ^ (prefixWord ++ tailWord_2306083).sum := by decide
  have hdescent : baseEnd_2306083 < baseStart_2306083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306088 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2306088 : Nat := 118140960795 + 2306088 * 2 ^ 59
def prefixEnd_2306088 : Nat := 4983230072969 + 3 ^ 40 * 2306088 * 2
def baseEnd_2306088 : Nat := 1184131575565678653794501

theorem tailTrace_2306088 : CollatzResearch.WordTrace tailWord_2306088 prefixEnd_2306088 1184131575565678653794501 := by
  unfold tailWord_2306088
  simp only [CollatzResearch.WordTrace]
  refine ⟨42054969634722249659815459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56073292846296332879753945 42054969634722249659815459)
  ·
    refine ⟨63082454452083374489723189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42054969634722249659815459 63082454452083374489723189)
    ·
      refine ⟨5913980104882816358411549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63082454452083374489723189 5913980104882816358411549)
      ·
        refine ⟨2217742539331056134404331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5913980104882816358411549 2217742539331056134404331)
        ·
          refine ⟨3326613808996584201606497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217742539331056134404331 3326613808996584201606497)
          ·
            refine ⟨2494960356747438151204873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3326613808996584201606497 2494960356747438151204873)
            ·
              refine ⟨1871220267560578613403655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2494960356747438151204873 1871220267560578613403655)
              ·
                refine ⟨2806830401340867920105483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871220267560578613403655 2806830401340867920105483)
                ·
                  refine ⟨4210245602011301880158225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2806830401340867920105483 4210245602011301880158225)
                  ·
                    refine ⟨3157684201508476410118669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4210245602011301880158225 3157684201508476410118669)
                    ·
                      refine ⟨1184131575565678653794501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3157684201508476410118669 1184131575565678653794501)
                      ·
                        rfl

theorem cell23_2306088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2306088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306088 prefixEnd_2306088 := by exact prefixLift 2306088
  have htrace : WordTrace (prefixWord ++ tailWord_2306088) baseStart_2306088 baseEnd_2306088 := by
    simpa [prefixWord, tailWord_2306088, baseEnd_2306088] using wordTrace_append hprefix tailTrace_2306088
  have hstable : (prefixWord ++ tailWord_2306088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306088).length < 2 ^ (prefixWord ++ tailWord_2306088).sum := by decide
  have hdescent : baseEnd_2306088 < baseStart_2306088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 4, 2, 2]
def baseStart_2306107 : Nat := 118140960795 + 2306107 * 2 ^ 59
def prefixEnd_2306107 : Nat := 4983230072969 + 3 ^ 40 * 2306107 * 2
def baseEnd_2306107 : Nat := 1184141331698114079456913

theorem tailTrace_2306107 : CollatzResearch.WordTrace tailWord_2306107 prefixEnd_2306107 1184141331698114079456913 := by
  unfold tailWord_2306107
  simp only [CollatzResearch.WordTrace]
  refine ⟨84110632256375665564572575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56073754837583777043048383 84110632256375665564572575)
  ·
    refine ⟨126165948384563498346858863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84110632256375665564572575 126165948384563498346858863)
    ·
      refine ⟨189248922576845247520288295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126165948384563498346858863 189248922576845247520288295)
      ·
        refine ⟨283873383865267871280432443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189248922576845247520288295 283873383865267871280432443)
        ·
          refine ⟨425810075797901806920648665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283873383865267871280432443 425810075797901806920648665)
          ·
            refine ⟨319357556848426355190486499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425810075797901806920648665 319357556848426355190486499)
            ·
              refine ⟨479036335272639532785729749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319357556848426355190486499 479036335272639532785729749)
              ·
                refine ⟨11227414107952489049665541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 479036335272639532785729749 11227414107952489049665541)
                ·
                  refine ⟨2105140145241091696812289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11227414107952489049665541 2105140145241091696812289)
                  ·
                    refine ⟨1578855108930818772609217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105140145241091696812289 1578855108930818772609217)
                    ·
                      refine ⟨1184141331698114079456913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578855108930818772609217 1184141331698114079456913)
                      ·
                        rfl

theorem cell23_2306107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 2, 2].length) (baseStart_2306107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306107 prefixEnd_2306107 := by exact prefixLift 2306107
  have htrace : WordTrace (prefixWord ++ tailWord_2306107) baseStart_2306107 baseEnd_2306107 := by
    simpa [prefixWord, tailWord_2306107, baseEnd_2306107] using wordTrace_append hprefix tailTrace_2306107
  have hstable : (prefixWord ++ tailWord_2306107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306107).length < 2 ^ (prefixWord ++ tailWord_2306107).sum := by decide
  have hdescent : baseEnd_2306107 < baseStart_2306107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306118 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2306118 : Nat := 118140960795 + 2306118 * 2 ^ 59
def prefixEnd_2306118 : Nat := 4983230072969 + 3 ^ 40 * 2306118 * 2
def baseEnd_2306118 : Nat := 1184146979985313536419363

theorem tailTrace_2306118 : CollatzResearch.WordTrace tailWord_2306118 prefixEnd_2306118 1184146979985313536419363 := by
  unfold tailWord_2306118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2628469795604244201350719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56074022306223876295482005 2628469795604244201350719)
  ·
    refine ⟨3942704693406366302026079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2628469795604244201350719 3942704693406366302026079)
    ·
      refine ⟨5914057040109549453039119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3942704693406366302026079 5914057040109549453039119)
      ·
        refine ⟨8871085560164324179558679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5914057040109549453039119 8871085560164324179558679)
        ·
          refine ⟨13306628340246486269338019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8871085560164324179558679 13306628340246486269338019)
          ·
            refine ⟨19959942510369729404007029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13306628340246486269338019 19959942510369729404007029)
            ·
              refine ⟨1871244610347162131625659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19959942510369729404007029 1871244610347162131625659)
              ·
                refine ⟨2806866915520743197438489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871244610347162131625659 2806866915520743197438489)
                ·
                  refine ⟨2105150186640557398078867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2806866915520743197438489 2105150186640557398078867)
                  ·
                    refine ⟨3157725279960836097118301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2105150186640557398078867 3157725279960836097118301)
                    ·
                      refine ⟨1184146979985313536419363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3157725279960836097118301 1184146979985313536419363)
                      ·
                        rfl

theorem cell23_2306118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2306118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306118 prefixEnd_2306118 := by exact prefixLift 2306118
  have htrace : WordTrace (prefixWord ++ tailWord_2306118) baseStart_2306118 baseEnd_2306118 := by
    simpa [prefixWord, tailWord_2306118, baseEnd_2306118] using wordTrace_append hprefix tailTrace_2306118
  have hstable : (prefixWord ++ tailWord_2306118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306118).length < 2 ^ (prefixWord ++ tailWord_2306118).sum := by decide
  have hdescent : baseEnd_2306118 < baseStart_2306118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306124 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 2, 2, 2]
def baseStart_2306124 : Nat := 118140960795 + 2306124 * 2 ^ 59
def prefixEnd_2306124 : Nat := 4983230072969 + 3 ^ 40 * 2306124 * 2
def baseEnd_2306124 : Nat := 1184150060869240512944335

theorem tailTrace_2306124 : CollatzResearch.WordTrace tailWord_2306124 prefixEnd_2306124 1184150060869240512944335 := by
  unfold tailWord_2306124
  simp only [CollatzResearch.WordTrace]
  refine ⟨42055626148657038733970713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56074168198209384978627617 42055626148657038733970713)
  ·
    refine ⟨31541719611492779050478035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42055626148657038733970713 31541719611492779050478035)
    ·
      refine ⟨47312579417239168575717053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31541719611492779050478035 47312579417239168575717053)
      ·
        refine ⟨17742217281464688215893895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47312579417239168575717053 17742217281464688215893895)
        ·
          refine ⟨26613325922197032323840843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17742217281464688215893895 26613325922197032323840843)
          ·
            refine ⟨39919988883295548485761265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26613325922197032323840843 39919988883295548485761265)
            ·
              refine ⟨29939991662471661364320949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39919988883295548485761265 29939991662471661364320949)
              ·
                refine ⟨2806874218356718252905089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29939991662471661364320949 2806874218356718252905089)
                ·
                  refine ⟨2105155663767538689678817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2806874218356718252905089 2105155663767538689678817)
                  ·
                    refine ⟨1578866747825654017259113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105155663767538689678817 1578866747825654017259113)
                    ·
                      refine ⟨1184150060869240512944335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578866747825654017259113 1184150060869240512944335)
                      ·
                        rfl

theorem cell23_2306124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_2306124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306124 prefixEnd_2306124 := by exact prefixLift 2306124
  have htrace : WordTrace (prefixWord ++ tailWord_2306124) baseStart_2306124 baseEnd_2306124 := by
    simpa [prefixWord, tailWord_2306124, baseEnd_2306124] using wordTrace_append hprefix tailTrace_2306124
  have hstable : (prefixWord ++ tailWord_2306124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306124).length < 2 ^ (prefixWord ++ tailWord_2306124).sum := by decide
  have hdescent : baseEnd_2306124 < baseStart_2306124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306141 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2306141 : Nat := 118140960795 + 2306141 * 2 ^ 59
def prefixEnd_2306141 : Nat := 4983230072969 + 3 ^ 40 * 2306141 * 2
def baseEnd_2306141 : Nat := 1184158790040366946431757

theorem tailTrace_2306141 : CollatzResearch.WordTrace tailWord_2306141 prefixEnd_2306141 1184158790040366946431757 := by
  unfold tailWord_2306141
  simp only [CollatzResearch.WordTrace]
  refine ⟨84111872338252489371310277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56074581558834992914206851 84111872338252489371310277)
  ·
    refine ⟨15770976063422341757120677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84111872338252489371310277 15770976063422341757120677)
    ·
      refine ⟨2957058011891689079460127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15770976063422341757120677 2957058011891689079460127)
      ·
        refine ⟨4435587017837533619190191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957058011891689079460127 4435587017837533619190191)
        ·
          refine ⟨6653380526756300428785287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435587017837533619190191 6653380526756300428785287)
          ·
            refine ⟨9980070790134450643177931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653380526756300428785287 9980070790134450643177931)
            ·
              refine ⟨14970106185201675964766897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9980070790134450643177931 14970106185201675964766897)
              ·
                refine ⟨11227579638901256973575173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14970106185201675964766897 11227579638901256973575173)
                ·
                  refine ⟨2105171182293985682545345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11227579638901256973575173 2105171182293985682545345)
                  ·
                    refine ⟨1578878386720489261909009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105171182293985682545345 1578878386720489261909009)
                    ·
                      refine ⟨1184158790040366946431757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1578878386720489261909009 1184158790040366946431757)
                      ·
                        rfl

theorem cell23_2306141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2306141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306141 prefixEnd_2306141 := by exact prefixLift 2306141
  have htrace : WordTrace (prefixWord ++ tailWord_2306141) baseStart_2306141 baseEnd_2306141 := by
    simpa [prefixWord, tailWord_2306141, baseEnd_2306141] using wordTrace_append hprefix tailTrace_2306141
  have hstable : (prefixWord ++ tailWord_2306141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306141).length < 2 ^ (prefixWord ++ tailWord_2306141).sum := by decide
  have hdescent : baseEnd_2306141 < baseStart_2306141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306147 : List Nat := [1, 1, 1, 5, 1, 1, 5, 3, 5]
def baseStart_2306147 : Nat := 118140960795 + 2306147 * 2 ^ 59
def prefixEnd_2306147 : Nat := 4983230072969 + 3 ^ 40 * 2306147 * 2
def baseEnd_2306147 : Nat := 131573541213810435884081

theorem tailTrace_2306147 : CollatzResearch.WordTrace tailWord_2306147 prefixEnd_2306147 131573541213810435884081 := by
  unfold tailWord_2306147
  simp only [CollatzResearch.WordTrace]
  refine ⟨84112091176230752396028695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56074727450820501597352463 84112091176230752396028695)
  ·
    refine ⟨126168136764346128594043043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84112091176230752396028695 126168136764346128594043043)
    ·
      refine ⟨189252205146519192891064565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126168136764346128594043043 189252205146519192891064565)
      ·
        refine ⟨17742394232486174333537303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189252205146519192891064565 17742394232486174333537303)
        ·
          refine ⟨26613591348729261500305955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17742394232486174333537303 26613591348729261500305955)
          ·
            refine ⟨39920387023093892250458933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26613591348729261500305955 39920387023093892250458933)
            ·
              refine ⟨3742536283415052398480525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39920387023093892250458933 3742536283415052398480525)
              ·
                refine ⟨1403451106280644649430197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3742536283415052398480525 1403451106280644649430197)
                ·
                  refine ⟨131573541213810435884081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1403451106280644649430197 131573541213810435884081)
                  ·
                    rfl

theorem cell23_2306147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 5].length) (baseStart_2306147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306147 prefixEnd_2306147 := by exact prefixLift 2306147
  have htrace : WordTrace (prefixWord ++ tailWord_2306147) baseStart_2306147 baseEnd_2306147 := by
    simpa [prefixWord, tailWord_2306147, baseEnd_2306147] using wordTrace_append hprefix tailTrace_2306147
  have hstable : (prefixWord ++ tailWord_2306147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306147).length < 2 ^ (prefixWord ++ tailWord_2306147).sum := by decide
  have hdescent : baseEnd_2306147 < baseStart_2306147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306160 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 4, 5]
def baseStart_2306160 : Nat := 118140960795 + 2306160 * 2 ^ 59
def prefixEnd_2306160 : Nat := 4983230072969 + 3 ^ 40 * 2306160 * 2
def baseEnd_2306160 : Nat := 394722848724267457364723

theorem tailTrace_2306160 : CollatzResearch.WordTrace tailWord_2306160 prefixEnd_2306160 394722848724267457364723 := by
  unfold tailWord_2306160
  simp only [CollatzResearch.WordTrace]
  refine ⟨42056282662591827808125967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56075043550122437077501289 42056282662591827808125967)
  ·
    refine ⟨63084423993887741712188951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42056282662591827808125967 63084423993887741712188951)
    ·
      refine ⟨94626635990831612568283427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63084423993887741712188951 94626635990831612568283427)
      ·
        refine ⟨141939953986247418852425141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94626635990831612568283427 141939953986247418852425141)
        ·
          refine ⟨13306870686210695517414857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141939953986247418852425141 13306870686210695517414857)
          ·
            refine ⟨9980153014658021638061143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13306870686210695517414857 9980153014658021638061143)
            ·
              refine ⟨14970229521987032457091715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9980153014658021638061143 14970229521987032457091715)
              ·
                refine ⟨22455344282980548685637573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14970229521987032457091715 22455344282980548685637573)
                ·
                  refine ⟨4210377053058852878557045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22455344282980548685637573 4210377053058852878557045)
                  ·
                    refine ⟨394722848724267457364723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4210377053058852878557045 394722848724267457364723)
                    ·
                      rfl

theorem cell23_2306160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_2306160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306160 prefixEnd_2306160 := by exact prefixLift 2306160
  have htrace : WordTrace (prefixWord ++ tailWord_2306160) baseStart_2306160 baseEnd_2306160 := by
    simpa [prefixWord, tailWord_2306160, baseEnd_2306160] using wordTrace_append hprefix tailTrace_2306160
  have hstable : (prefixWord ++ tailWord_2306160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306160).length < 2 ^ (prefixWord ++ tailWord_2306160).sum := by decide
  have hdescent : baseEnd_2306160 < baseStart_2306160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306163 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 8]
def baseStart_2306163 : Nat := 118140960795 + 2306163 * 2 ^ 59
def prefixEnd_2306163 : Nat := 4983230072969 + 3 ^ 40 * 2306163 * 2
def baseEnd_2306163 : Nat := 1184170086614765860356655

theorem tailTrace_2306163 : CollatzResearch.WordTrace tailWord_2306163 prefixEnd_2306163 1184170086614765860356655 := by
  unfold tailWord_2306163
  simp only [CollatzResearch.WordTrace]
  refine ⟨84112674744172787128611143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56075116496115191419074095 84112674744172787128611143)
  ·
    refine ⟨126169012116259180692916715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84112674744172787128611143 126169012116259180692916715)
    ·
      refine ⟨189253518174388771039375073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126169012116259180692916715 189253518174388771039375073)
      ·
        refine ⟨141940138630791578279531305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189253518174388771039375073 141940138630791578279531305)
        ·
          refine ⟨106455103973093683709648479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141940138630791578279531305 106455103973093683709648479)
          ·
            refine ⟨159682655959640525564472719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106455103973093683709648479 159682655959640525564472719)
            ·
              refine ⟨239523983939460788346709079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159682655959640525564472719 239523983939460788346709079)
              ·
                refine ⟨359285975909191182520063619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239523983939460788346709079 359285975909191182520063619)
                ·
                  refine ⟨538928963863786773780095429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359285975909191182520063619 538928963863786773780095429)
                  ·
                    refine ⟨101049180724460020083767893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 538928963863786773780095429 101049180724460020083767893)
                    ·
                      refine ⟨1184170086614765860356655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 101049180724460020083767893 1184170086614765860356655)
                      ·
                        rfl

theorem cell23_2306163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_2306163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306163 prefixEnd_2306163 := by exact prefixLift 2306163
  have htrace : WordTrace (prefixWord ++ tailWord_2306163) baseStart_2306163 baseEnd_2306163 := by
    simpa [prefixWord, tailWord_2306163, baseEnd_2306163] using wordTrace_append hprefix tailTrace_2306163
  have hstable : (prefixWord ++ tailWord_2306163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306163).length < 2 ^ (prefixWord ++ tailWord_2306163).sum := by decide
  have hdescent : baseEnd_2306163 < baseStart_2306163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306197 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_2306197 : Nat := 118140960795 + 2306197 * 2 ^ 59
def prefixEnd_2306197 : Nat := 4983230072969 + 3 ^ 40 * 2306197 * 2
def baseEnd_2306197 : Nat := 1184187544957018727331499

theorem tailTrace_2306197 : CollatzResearch.WordTrace tailWord_2306197 prefixEnd_2306197 1184187544957018727331499 := by
  unfold tailWord_2306197
  simp only [CollatzResearch.WordTrace]
  refine ⟨84113914826049610935348845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56075943217366407290232563 84113914826049610935348845)
  ·
    refine ⟨31542718059768604100755817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84113914826049610935348845 31542718059768604100755817)
    ·
      refine ⟨23657038544826453075566863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31542718059768604100755817 23657038544826453075566863)
      ·
        refine ⟨35485557817239679613350295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23657038544826453075566863 35485557817239679613350295)
        ·
          refine ⟨53228336725859519420025443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35485557817239679613350295 53228336725859519420025443)
          ·
            refine ⟨79842505088789279130038165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53228336725859519420025443 79842505088789279130038165)
            ·
              refine ⟨3742617426036997459220539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79842505088789279130038165 3742617426036997459220539)
              ·
                refine ⟨5613926139055496188830809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742617426036997459220539 5613926139055496188830809)
                ·
                  refine ⟨4210444604291622141623107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5613926139055496188830809 4210444604291622141623107)
                  ·
                    refine ⟨6315666906437433212434661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210444604291622141623107 6315666906437433212434661)
                    ·
                      refine ⟨1184187544957018727331499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6315666906437433212434661 1184187544957018727331499)
                      ·
                        rfl

theorem cell23_2306197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_2306197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306197 prefixEnd_2306197 := by exact prefixLift 2306197
  have htrace : WordTrace (prefixWord ++ tailWord_2306197) baseStart_2306197 baseEnd_2306197 := by
    simpa [prefixWord, tailWord_2306197, baseEnd_2306197] using wordTrace_append hprefix tailTrace_2306197
  have hstable : (prefixWord ++ tailWord_2306197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306197).length < 2 ^ (prefixWord ++ tailWord_2306197).sum := by decide
  have hdescent : baseEnd_2306197 < baseStart_2306197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306241 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2306241 : Nat := 118140960795 + 2306241 * 2 ^ 59
def prefixEnd_2306241 : Nat := 4983230072969 + 3 ^ 40 * 2306241 * 2
def baseEnd_2306241 : Nat := 394736712701938851727099

theorem tailTrace_2306241 : CollatzResearch.WordTrace tailWord_2306241 prefixEnd_2306241 394736712701938851727099 := by
  unfold tailWord_2306241
  simp only [CollatzResearch.WordTrace]
  refine ⟨84115519637890206449950577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56077013091926804299967051 84115519637890206449950577)
  ·
    refine ⟨63086639728417654837462933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84115519637890206449950577 63086639728417654837462933)
    ·
      refine ⟨2957186237269577570506075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63086639728417654837462933 2957186237269577570506075)
      ·
        refine ⟨4435779355904366355759113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957186237269577570506075 4435779355904366355759113)
        ·
          refine ⟨3326834516928274766819335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4435779355904366355759113 3326834516928274766819335)
          ·
            refine ⟨4990251775392412150229003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326834516928274766819335 4990251775392412150229003)
            ·
              refine ⟨7485377663088618225343505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990251775392412150229003 7485377663088618225343505)
              ·
                refine ⟨5614033247316463669007629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7485377663088618225343505 5614033247316463669007629)
                ·
                  refine ⟨2105262467743673875877861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5614033247316463669007629 2105262467743673875877861)
                  ·
                    refine ⟨394736712701938851727099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2105262467743673875877861 394736712701938851727099)
                    ·
                      rfl

theorem cell23_2306241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2306241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306241 prefixEnd_2306241 := by exact prefixLift 2306241
  have htrace : WordTrace (prefixWord ++ tailWord_2306241) baseStart_2306241 baseEnd_2306241 := by
    simpa [prefixWord, tailWord_2306241, baseEnd_2306241] using wordTrace_append hprefix tailTrace_2306241
  have hstable : (prefixWord ++ tailWord_2306241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306241).length < 2 ^ (prefixWord ++ tailWord_2306241).sum := by decide
  have hdescent : baseEnd_2306241 < baseStart_2306241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306327 : List Nat := [1, 1, 3, 4, 1, 4, 9]
def baseStart_2306327 : Nat := 118140960795 + 2306327 * 2 ^ 59
def prefixEnd_2306327 : Nat := 4983230072969 + 3 ^ 40 * 2306327 * 2
def baseEnd_2306327 : Nat := 14620423425211150848221

theorem tailTrace_2306327 : CollatzResearch.WordTrace tailWord_2306327 prefixEnd_2306327 14620423425211150848221 := by
  unfold tailWord_2306327
  simp only [CollatzResearch.WordTrace]
  refine ⟨84118656315578643137581235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56079104210385762091720823 84118656315578643137581235)
  ·
    refine ⟨126177984473367964706371853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84118656315578643137581235 126177984473367964706371853)
    ·
      refine ⟨47316744177512986764889445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126177984473367964706371853 47316744177512986764889445)
      ·
        refine ⟨8871889533283685018416771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47316744177512986764889445 8871889533283685018416771)
        ·
          refine ⟨13307834299925527527625157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8871889533283685018416771 13307834299925527527625157)
          ·
            refine ⟨2495218931236036411429717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13307834299925527527625157 2495218931236036411429717)
            ·
              refine ⟨14620423425211150848221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2495218931236036411429717 14620423425211150848221)
              ·
                rfl

theorem cell23_2306327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 9].length) (baseStart_2306327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306327 prefixEnd_2306327 := by exact prefixLift 2306327
  have htrace : WordTrace (prefixWord ++ tailWord_2306327) baseStart_2306327 baseEnd_2306327 := by
    simpa [prefixWord, tailWord_2306327, baseEnd_2306327] using wordTrace_append hprefix tailTrace_2306327
  have hstable : (prefixWord ++ tailWord_2306327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306327).length < 2 ^ (prefixWord ++ tailWord_2306327).sum := by decide
  have hdescent : baseEnd_2306327 < baseStart_2306327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306338 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_2306338 : Nat := 118140960795 + 2306338 * 2 ^ 59
def prefixEnd_2306338 : Nat := 4983230072969 + 3 ^ 40 * 2306338 * 2
def baseEnd_2306338 : Nat := 1184259945729302675668351

theorem tailTrace_2306338 : CollatzResearch.WordTrace tailWord_2306338 prefixEnd_2306338 1184259945729302675668351 := by
  unfold tailWord_2306338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21029764379634698004057917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56079371679025861344154445 21029764379634698004057917)
  ·
    refine ⟨7886161642363011751521719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21029764379634698004057917 7886161642363011751521719)
    ·
      refine ⟨11829242463544517627282579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7886161642363011751521719 11829242463544517627282579)
      ·
        refine ⟨17743863695316776440923869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11829242463544517627282579 17743863695316776440923869)
        ·
          refine ⟨6653948885743791165346451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17743863695316776440923869 6653948885743791165346451)
          ·
            refine ⟨9980923328615686748019677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653948885743791165346451 9980923328615686748019677)
            ·
              refine ⟨3742846248230882530507379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9980923328615686748019677 3742846248230882530507379)
              ·
                refine ⟨5614269372346323795761069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742846248230882530507379 5614269372346323795761069)
                ·
                  refine ⟨2105351014629871423410401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5614269372346323795761069 2105351014629871423410401)
                  ·
                    refine ⟨1579013260972403567557801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105351014629871423410401 1579013260972403567557801)
                    ·
                      refine ⟨1184259945729302675668351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579013260972403567557801 1184259945729302675668351)
                      ·
                        rfl

theorem cell23_2306338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_2306338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306338 prefixEnd_2306338 := by exact prefixLift 2306338
  have htrace : WordTrace (prefixWord ++ tailWord_2306338) baseStart_2306338 baseEnd_2306338 := by
    simpa [prefixWord, tailWord_2306338, baseEnd_2306338] using wordTrace_append hprefix tailTrace_2306338
  have hstable : (prefixWord ++ tailWord_2306338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306338).length < 2 ^ (prefixWord ++ tailWord_2306338).sum := by decide
  have hdescent : baseEnd_2306338 < baseStart_2306338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306344 : List Nat := [2, 1, 5, 1, 3, 1, 2, 8]
def baseStart_2306344 : Nat := 118140960795 + 2306344 * 2 ^ 59
def prefixEnd_2306344 : Nat := 4983230072969 + 3 ^ 40 * 2306344 * 2
def baseEnd_2306344 : Nat := 43861593578267764896049

theorem tailTrace_2306344 : CollatzResearch.WordTrace tailWord_2306344 prefixEnd_2306344 43861593578267764896049 := by
  unfold tailWord_2306344
  simp only [CollatzResearch.WordTrace]
  refine ⟨42059638178258527520475043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56079517571011370027300057 42059638178258527520475043)
  ·
    refine ⟨63089457267387791280712565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42059638178258527520475043 63089457267387791280712565)
    ·
      refine ⟨5914636618817605432566803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63089457267387791280712565 5914636618817605432566803)
      ·
        refine ⟨8871954928226408148850205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5914636618817605432566803 8871954928226408148850205)
        ·
          refine ⟨3326983098084903055818827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8871954928226408148850205 3326983098084903055818827)
          ·
            refine ⟨4990474647127354583728241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326983098084903055818827 4990474647127354583728241)
            ·
              refine ⟨3742855985345515937796181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4990474647127354583728241 3742855985345515937796181)
              ·
                refine ⟨43861593578267764896049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3742855985345515937796181 43861593578267764896049)
                ·
                  rfl

theorem cell23_2306344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 8].length) (baseStart_2306344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306344 prefixEnd_2306344 := by exact prefixLift 2306344
  have htrace : WordTrace (prefixWord ++ tailWord_2306344) baseStart_2306344 baseEnd_2306344 := by
    simpa [prefixWord, tailWord_2306344, baseEnd_2306344] using wordTrace_append hprefix tailTrace_2306344
  have hstable : (prefixWord ++ tailWord_2306344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306344).length < 2 ^ (prefixWord ++ tailWord_2306344).sum := by decide
  have hdescent : baseEnd_2306344 < baseStart_2306344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306388 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_2306388 : Nat := 118140960795 + 2306388 * 2 ^ 59
def prefixEnd_2306388 : Nat := 4983230072969 + 3 ^ 40 * 2306388 * 2
def baseEnd_2306388 : Nat := 1184285619762027480043121

theorem tailTrace_2306388 : CollatzResearch.WordTrace tailWord_2306388 prefixEnd_2306388 1184285619762027480043121 := by
  unfold tailWord_2306388
  simp only [CollatzResearch.WordTrace]
  refine ⟨42060440584178825277775909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56080587445571767037034545 42060440584178825277775909)
  ·
    refine ⟨7886332609533529739582983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42060440584178825277775909 7886332609533529739582983)
    ·
      refine ⟨11829498914300294609374475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7886332609533529739582983 11829498914300294609374475)
      ·
        refine ⟨17744248371450441914061713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11829498914300294609374475 17744248371450441914061713)
        ·
          refine ⟨13308186278587831435546285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17744248371450441914061713 13308186278587831435546285)
          ·
            refine ⟨4990569854470436788329857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13308186278587831435546285 4990569854470436788329857)
            ·
              refine ⟨3742927390852827591247393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4990569854470436788329857 3742927390852827591247393)
              ·
                refine ⟨2807195543139620693435545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3742927390852827591247393 2807195543139620693435545)
                ·
                  refine ⟨2105396657354715520076659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2807195543139620693435545 2105396657354715520076659)
                  ·
                    refine ⟨3158094986032073280114989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2105396657354715520076659 3158094986032073280114989)
                    ·
                      refine ⟨1184285619762027480043121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3158094986032073280114989 1184285619762027480043121)
                      ·
                        rfl

theorem cell23_2306388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_2306388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306388 prefixEnd_2306388 := by exact prefixLift 2306388
  have htrace : WordTrace (prefixWord ++ tailWord_2306388) baseStart_2306388 baseEnd_2306388 := by
    simpa [prefixWord, tailWord_2306388, baseEnd_2306388] using wordTrace_append hprefix tailTrace_2306388
  have hstable : (prefixWord ++ tailWord_2306388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306388).length < 2 ^ (prefixWord ++ tailWord_2306388).sum := by decide
  have hdescent : baseEnd_2306388 < baseStart_2306388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306389 : List Nat := [1, 3, 2, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_2306389 : Nat := 118140960795 + 2306389 * 2 ^ 59
def prefixEnd_2306389 : Nat := 4983230072969 + 3 ^ 40 * 2306389 * 2
def baseEnd_2306389 : Nat := 1184286133242681976130617

theorem tailTrace_2306389 : CollatzResearch.WordTrace tailWord_2306389 prefixEnd_2306389 1184286133242681976130617 := by
  unfold tailWord_2306389
  simp only [CollatzResearch.WordTrace]
  refine ⟨84120917641354027726338221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56080611760902685150892147 84120917641354027726338221)
  ·
    refine ⟨31545344115507760397376833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84120917641354027726338221 31545344115507760397376833)
    ·
      refine ⟨23659008086630820298032625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31545344115507760397376833 23659008086630820298032625)
      ·
        refine ⟨17744256064973115223524469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23659008086630820298032625 17744256064973115223524469)
        ·
          refine ⟨1663524006091229552205419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17744256064973115223524469 1663524006091229552205419)
          ·
            refine ⟨2495286009136844328308129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663524006091229552205419 2495286009136844328308129)
            ·
              refine ⟨1871464506852633246231097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2495286009136844328308129 1871464506852633246231097)
              ·
                refine ⟨1403598380139474934673323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871464506852633246231097 1403598380139474934673323)
                ·
                  refine ⟨2105397570209212402009985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403598380139474934673323 2105397570209212402009985)
                  ·
                    refine ⟨1579048177656909301507489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105397570209212402009985 1579048177656909301507489)
                    ·
                      refine ⟨1184286133242681976130617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579048177656909301507489 1184286133242681976130617)
                      ·
                        rfl

theorem cell23_2306389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_2306389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306389 prefixEnd_2306389 := by exact prefixLift 2306389
  have htrace : WordTrace (prefixWord ++ tailWord_2306389) baseStart_2306389 baseEnd_2306389 := by
    simpa [prefixWord, tailWord_2306389, baseEnd_2306389] using wordTrace_append hprefix tailTrace_2306389
  have hstable : (prefixWord ++ tailWord_2306389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306389).length < 2 ^ (prefixWord ++ tailWord_2306389).sum := by decide
  have hdescent : baseEnd_2306389 < baseStart_2306389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306394 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2]
def baseStart_2306394 : Nat := 118140960795 + 2306394 * 2 ^ 59
def prefixEnd_2306394 : Nat := 4983230072969 + 3 ^ 40 * 2306394 * 2
def baseEnd_2306394 : Nat := 1184288700645954456568093

theorem tailTrace_2306394 : CollatzResearch.WordTrace tailWord_2306394 prefixEnd_2306394 1184288700645954456568093 := by
  unfold tailWord_2306394
  simp only [CollatzResearch.WordTrace]
  refine ⟨21030275001583978395067559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56080733337557275720180157 21030275001583978395067559)
  ·
    refine ⟨31545412502375967592601339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21030275001583978395067559 31545412502375967592601339)
    ·
      refine ⟨47318118753563951388902009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31545412502375967592601339 47318118753563951388902009)
      ·
        refine ⟨35488589065172963541676507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47318118753563951388902009 35488589065172963541676507)
        ·
          refine ⟨53232883597759445312514761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35488589065172963541676507 53232883597759445312514761)
          ·
            refine ⟨39924662698319583984386071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53232883597759445312514761 39924662698319583984386071)
            ·
              refine ⟨59886994047479375976579107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39924662698319583984386071 59886994047479375976579107)
              ·
                refine ⟨89830491071219063964868661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59886994047479375976579107 89830491071219063964868661)
                ·
                  refine ⟨8421608537926787246706437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89830491071219063964868661 8421608537926787246706437)
                  ·
                    refine ⟨1579051600861272608757457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8421608537926787246706437 1579051600861272608757457)
                    ·
                      refine ⟨1184288700645954456568093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579051600861272608757457 1184288700645954456568093)
                      ·
                        rfl

theorem cell23_2306394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_2306394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306394 prefixEnd_2306394 := by exact prefixLift 2306394
  have htrace : WordTrace (prefixWord ++ tailWord_2306394) baseStart_2306394 baseEnd_2306394 := by
    simpa [prefixWord, tailWord_2306394, baseEnd_2306394] using wordTrace_append hprefix tailTrace_2306394
  have hstable : (prefixWord ++ tailWord_2306394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306394).length < 2 ^ (prefixWord ++ tailWord_2306394).sum := by decide
  have hdescent : baseEnd_2306394 < baseStart_2306394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306444 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_2306444 : Nat := 118140960795 + 2306444 * 2 ^ 59
def prefixEnd_2306444 : Nat := 4983230072969 + 3 ^ 40 * 2306444 * 2
def baseEnd_2306444 : Nat := 1184314374678679260942863

theorem tailTrace_2306444 : CollatzResearch.WordTrace tailWord_2306444 prefixEnd_2306444 1184314374678679260942863 := by
  unfold tailWord_2306444
  simp only [CollatzResearch.WordTrace]
  refine ⟨42061461828077386059795193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56081949104103181413060257 42061461828077386059795193)
  ·
    refine ⟨31546096371058039544846395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42061461828077386059795193 31546096371058039544846395)
    ·
      refine ⟨47319144556587059317269593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31546096371058039544846395 47319144556587059317269593)
      ·
        refine ⟨35489358417440294487952195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47319144556587059317269593 35489358417440294487952195)
        ·
          refine ⟨53234037626160441731928293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35489358417440294487952195 53234037626160441731928293)
          ·
            refine ⟨9981382054905082824736555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53234037626160441731928293 9981382054905082824736555)
            ·
              refine ⟨14972073082357624237104833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9981382054905082824736555 14972073082357624237104833)
              ·
                refine ⟨11229054811768218177828625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14972073082357624237104833 11229054811768218177828625)
                ·
                  refine ⟨8421791108826163633371469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11229054811768218177828625 8421791108826163633371469)
                  ·
                    refine ⟨3158171665809811362514301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8421791108826163633371469 3158171665809811362514301)
                    ·
                      refine ⟨1184314374678679260942863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3158171665809811362514301 1184314374678679260942863)
                      ·
                        rfl

theorem cell23_2306444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_2306444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306444 prefixEnd_2306444 := by exact prefixLift 2306444
  have htrace : WordTrace (prefixWord ++ tailWord_2306444) baseStart_2306444 baseEnd_2306444 := by
    simpa [prefixWord, tailWord_2306444, baseEnd_2306444] using wordTrace_append hprefix tailTrace_2306444
  have hstable : (prefixWord ++ tailWord_2306444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306444).length < 2 ^ (prefixWord ++ tailWord_2306444).sum := by decide
  have hdescent : baseEnd_2306444 < baseStart_2306444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306457 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_2306457 : Nat := 118140960795 + 2306457 * 2 ^ 59
def prefixEnd_2306457 : Nat := 4983230072969 + 3 ^ 40 * 2306457 * 2
def baseEnd_2306457 : Nat := 1184321049927187710080303

theorem tailTrace_2306457 : CollatzResearch.WordTrace tailWord_2306457 prefixEnd_2306457 1184321049927187710080303 := by
  unfold tailWord_2306457
  simp only [CollatzResearch.WordTrace]
  refine ⟨84123397805107675339813625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56082265203405116893209083 84123397805107675339813625)
  ·
    refine ⟨63092548353830756504860219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84123397805107675339813625 63092548353830756504860219)
    ·
      refine ⟨94638822530746134757290329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63092548353830756504860219 94638822530746134757290329)
      ·
        refine ⟨70979116898059601067967747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94638822530746134757290329 70979116898059601067967747)
        ·
          refine ⟨106468675347089401601951621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70979116898059601067967747 106468675347089401601951621)
          ·
            refine ⟨19962876627579262800365929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106468675347089401601951621 19962876627579262800365929)
            ·
              refine ⟨14972157470684447100274447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19962876627579262800365929 14972157470684447100274447)
              ·
                refine ⟨22458236206026670650411671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14972157470684447100274447 22458236206026670650411671)
                ·
                  refine ⟨33687354309040005975617507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22458236206026670650411671 33687354309040005975617507)
                  ·
                    refine ⟨50531031463560008963426261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33687354309040005975617507 50531031463560008963426261)
                    ·
                      refine ⟨1184321049927187710080303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50531031463560008963426261 1184321049927187710080303)
                      ·
                        rfl

theorem cell23_2306457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_2306457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306457 prefixEnd_2306457 := by exact prefixLift 2306457
  have htrace : WordTrace (prefixWord ++ tailWord_2306457) baseStart_2306457 baseEnd_2306457 := by
    simpa [prefixWord, tailWord_2306457, baseEnd_2306457] using wordTrace_append hprefix tailTrace_2306457
  have hstable : (prefixWord ++ tailWord_2306457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306457).length < 2 ^ (prefixWord ++ tailWord_2306457).sum := by decide
  have hdescent : baseEnd_2306457 < baseStart_2306457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306485 : List Nat := [1, 3, 3, 2, 4, 1, 1, 3, 5]
def baseStart_2306485 : Nat := 118140960795 + 2306485 * 2 ^ 59
def prefixEnd_2306485 : Nat := 4983230072969 + 3 ^ 40 * 2306485 * 2
def baseEnd_2306485 : Nat := 131592825265057066725575

theorem tailTrace_2306485 : CollatzResearch.WordTrace tailWord_2306485 prefixEnd_2306485 131592825265057066725575 := by
  unfold tailWord_2306485
  simp only [CollatzResearch.WordTrace]
  refine ⟨84124419049006236121832909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56082946032670824081221939 84124419049006236121832909)
  ·
    refine ⟨31546657143377338545687341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84124419049006236121832909 31546657143377338545687341)
    ·
      refine ⟨11829996428766501954632753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31546657143377338545687341 11829996428766501954632753)
      ·
        refine ⟨8872497321574876465974565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11829996428766501954632753 8872497321574876465974565)
        ·
          refine ⟨1663593247795289337370231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8872497321574876465974565 1663593247795289337370231)
          ·
            refine ⟨2495389871692934006055347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663593247795289337370231 2495389871692934006055347)
            ·
              refine ⟨3743084807539401009083021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495389871692934006055347 3743084807539401009083021)
              ·
                refine ⟨1403656802827275378406133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3743084807539401009083021 1403656802827275378406133)
                ·
                  refine ⟨131592825265057066725575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1403656802827275378406133 131592825265057066725575)
                  ·
                    rfl

theorem cell23_2306485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_2306485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306485 prefixEnd_2306485 := by exact prefixLift 2306485
  have htrace : WordTrace (prefixWord ++ tailWord_2306485) baseStart_2306485 baseEnd_2306485 := by
    simpa [prefixWord, tailWord_2306485, baseEnd_2306485] using wordTrace_append hprefix tailTrace_2306485
  have hstable : (prefixWord ++ tailWord_2306485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306485).length < 2 ^ (prefixWord ++ tailWord_2306485).sum := by decide
  have hdescent : baseEnd_2306485 < baseStart_2306485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306518 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_2306518 : Nat := 118140960795 + 2306518 * 2 ^ 59
def prefixEnd_2306518 : Nat := 4983230072969 + 3 ^ 40 * 2306518 * 2
def baseEnd_2306518 : Nat := 1184352372247111971417523

theorem tailTrace_2306518 : CollatzResearch.WordTrace tailWord_2306518 prefixEnd_2306518 1184352372247111971417523 := by
  unfold tailWord_2306518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5257851416117917672361513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56083748438591121838522805 5257851416117917672361513)
  ·
    refine ⟨3943388562088438254271135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5257851416117917672361513 3943388562088438254271135)
    ·
      refine ⟨5915082843132657381406703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3943388562088438254271135 5915082843132657381406703)
      ·
        refine ⟨8872624264698986072110055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915082843132657381406703 8872624264698986072110055)
        ·
          refine ⟨13308936397048479108165083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8872624264698986072110055 13308936397048479108165083)
          ·
            refine ⟨19963404595572718662247625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13308936397048479108165083 19963404595572718662247625)
            ·
              refine ⟨14972553446679538996685719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19963404595572718662247625 14972553446679538996685719)
              ·
                refine ⟨22458830170019308495028579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14972553446679538996685719 22458830170019308495028579)
                ·
                  refine ⟨33688245255028962742542869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22458830170019308495028579 33688245255028962742542869)
                  ·
                    refine ⟨1579136496329482628556697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33688245255028962742542869 1579136496329482628556697)
                    ·
                      refine ⟨1184352372247111971417523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579136496329482628556697 1184352372247111971417523)
                      ·
                        rfl

theorem cell23_2306518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_2306518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306518 prefixEnd_2306518 := by exact prefixLift 2306518
  have htrace : WordTrace (prefixWord ++ tailWord_2306518) baseStart_2306518 baseEnd_2306518 := by
    simpa [prefixWord, tailWord_2306518, baseEnd_2306518] using wordTrace_append hprefix tailTrace_2306518
  have hstable : (prefixWord ++ tailWord_2306518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306518).length < 2 ^ (prefixWord ++ tailWord_2306518).sum := by decide
  have hdescent : baseEnd_2306518 < baseStart_2306518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306538 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2306538 : Nat := 118140960795 + 2306538 * 2 ^ 59
def prefixEnd_2306538 : Nat := 4983230072969 + 3 ^ 40 * 2306538 * 2
def baseEnd_2306538 : Nat := 1184362641860201893167431

theorem tailTrace_2306538 : CollatzResearch.WordTrace tailWord_2306538 prefixEnd_2306538 1184362641860201893167431 := by
  unfold tailWord_2306538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21031588029453556543378067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56084234745209484115674845 21031588029453556543378067)
  ·
    refine ⟨31547382044180334815067101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21031588029453556543378067 31547382044180334815067101)
    ·
      refine ⟨11830268266567625555650163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31547382044180334815067101 11830268266567625555650163)
      ·
        refine ⟨17745402399851438333475245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11830268266567625555650163 17745402399851438333475245)
        ·
          refine ⟨6654525899944289375053217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17745402399851438333475245 6654525899944289375053217)
          ·
            refine ⟨4990894424958217031289913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6654525899944289375053217 4990894424958217031289913)
            ·
              refine ⟨3743170818718662773467435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4990894424958217031289913 3743170818718662773467435)
              ·
                refine ⟨5614756228077994160201153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3743170818718662773467435 5614756228077994160201153)
                ·
                  refine ⟨4211067171058495620150865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5614756228077994160201153 4211067171058495620150865)
                  ·
                    refine ⟨3158300378293871715113149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4211067171058495620150865 3158300378293871715113149)
                    ·
                      refine ⟨1184362641860201893167431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3158300378293871715113149 1184362641860201893167431)
                      ·
                        rfl

theorem cell23_2306538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2306538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306538 prefixEnd_2306538 := by exact prefixLift 2306538
  have htrace : WordTrace (prefixWord ++ tailWord_2306538) baseStart_2306538 baseEnd_2306538 := by
    simpa [prefixWord, tailWord_2306538, baseEnd_2306538] using wordTrace_append hprefix tailTrace_2306538
  have hstable : (prefixWord ++ tailWord_2306538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306538).length < 2 ^ (prefixWord ++ tailWord_2306538).sum := by decide
  have hdescent : baseEnd_2306538 < baseStart_2306538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306562 : List Nat := [3, 4, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2306562 : Nat := 118140960795 + 2306562 * 2 ^ 59
def prefixEnd_2306562 : Nat := 4983230072969 + 3 ^ 40 * 2306562 * 2
def baseEnd_2306562 : Nat := 394791655131969933089107

theorem tailTrace_2306562 : CollatzResearch.WordTrace tailWord_2306562 prefixEnd_2306562 394791655131969933089107 := by
  unfold tailWord_2306562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21031806867431819568096485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56084818313151518848257293 21031806867431819568096485)
  ·
    refine ⟨3943463787643466169018091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21031806867431819568096485 3943463787643466169018091)
    ·
      refine ⟨5915195681465199253527137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3943463787643466169018091 5915195681465199253527137)
      ·
        refine ⟨4436396761098899440145353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5915195681465199253527137 4436396761098899440145353)
        ·
          refine ⟨3327297570824174580109015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4436396761098899440145353 3327297570824174580109015)
          ·
            refine ⟨4990946356236261870163523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327297570824174580109015 4990946356236261870163523)
            ·
              refine ⟨7486419534354392805245285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990946356236261870163523 7486419534354392805245285)
              ·
                refine ⟨1403703662691448650983491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7486419534354392805245285 1403703662691448650983491)
                ·
                  refine ⟨2105555494037172976475237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403703662691448650983491 2105555494037172976475237)
                  ·
                    refine ⟨394791655131969933089107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2105555494037172976475237 394791655131969933089107)
                    ·
                      rfl

theorem cell23_2306562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2306562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306562 prefixEnd_2306562 := by exact prefixLift 2306562
  have htrace : WordTrace (prefixWord ++ tailWord_2306562) baseStart_2306562 baseEnd_2306562 := by
    simpa [prefixWord, tailWord_2306562, baseEnd_2306562] using wordTrace_append hprefix tailTrace_2306562
  have hstable : (prefixWord ++ tailWord_2306562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306562).length < 2 ^ (prefixWord ++ tailWord_2306562).sum := by decide
  have hdescent : baseEnd_2306562 < baseStart_2306562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306591 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 4]
def baseStart_2306591 : Nat := 118140960795 + 2306591 * 2 ^ 59
def prefixEnd_2306591 : Nat := 4983230072969 + 3 ^ 40 * 2306591 * 2
def baseEnd_2306591 : Nat := 1184389856334890185804687

theorem tailTrace_2306591 : CollatzResearch.WordTrace tailWord_2306591 prefixEnd_2306591 1184389856334890185804687 := by
  unfold tailWord_2306591
  simp only [CollatzResearch.WordTrace]
  refine ⟨84128285186622216225191627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56085523457748144150127751 84128285186622216225191627)
  ·
    refine ⟨126192427779933324337787441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84128285186622216225191627 126192427779933324337787441)
    ·
      refine ⟨94644320834949993253340581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126192427779933324337787441 94644320834949993253340581)
      ·
        refine ⟨17745810156553123735001359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94644320834949993253340581 17745810156553123735001359)
        ·
          refine ⟨26618715234829685602502039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17745810156553123735001359 26618715234829685602502039)
          ·
            refine ⟨39928072852244528403753059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26618715234829685602502039 39928072852244528403753059)
            ·
              refine ⟨59892109278366792605629589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39928072852244528403753059 59892109278366792605629589)
              ·
                refine ⟨2807442622423443403388887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59892109278366792605629589 2807442622423443403388887)
                ·
                  refine ⟨4211163933635165105083331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807442622423443403388887 4211163933635165105083331)
                  ·
                    refine ⟨6316745900452747657624997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4211163933635165105083331 6316745900452747657624997)
                    ·
                      refine ⟨1184389856334890185804687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6316745900452747657624997 1184389856334890185804687)
                      ·
                        rfl

theorem cell23_2306591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_2306591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306591 prefixEnd_2306591 := by exact prefixLift 2306591
  have htrace : WordTrace (prefixWord ++ tailWord_2306591) baseStart_2306591 baseEnd_2306591 := by
    simpa [prefixWord, tailWord_2306591, baseEnd_2306591] using wordTrace_append hprefix tailTrace_2306591
  have hstable : (prefixWord ++ tailWord_2306591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306591).length < 2 ^ (prefixWord ++ tailWord_2306591).sum := by decide
  have hdescent : baseEnd_2306591 < baseStart_2306591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306595 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 2, 3, 2]
def baseStart_2306595 : Nat := 118140960795 + 2306595 * 2 ^ 59
def prefixEnd_2306595 : Nat := 4983230072969 + 3 ^ 40 * 2306595 * 2
def baseEnd_2306595 : Nat := 1184391910257508170154669

theorem tailTrace_2306595 : CollatzResearch.WordTrace tailWord_2306595 prefixEnd_2306595 1184391910257508170154669 := by
  unfold tailWord_2306595
  simp only [CollatzResearch.WordTrace]
  refine ⟨84128431078607724908337239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56085620719071816605558159 84128431078607724908337239)
  ·
    refine ⟨126192646617911587362505859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84128431078607724908337239 126192646617911587362505859)
    ·
      refine ⟨189288969926867381043758789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126192646617911587362505859 189288969926867381043758789)
      ·
        refine ⟨35491681861287633945704773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189288969926867381043758789 35491681861287633945704773)
        ·
          refine ⟨6654690348991431364819645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35491681861287633945704773 6654690348991431364819645)
          ·
            refine ⟨2495508880871786761807367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6654690348991431364819645 2495508880871786761807367)
            ·
              refine ⟨3743263321307680142711051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495508880871786761807367 3743263321307680142711051)
              ·
                refine ⟨5614894981961520214066577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3743263321307680142711051 5614894981961520214066577)
                ·
                  refine ⟨4211171236471140160549933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5614894981961520214066577 4211171236471140160549933)
                  ·
                    refine ⟨1579189213676677560206225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4211171236471140160549933 1579189213676677560206225)
                    ·
                      refine ⟨1184391910257508170154669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579189213676677560206225 1184391910257508170154669)
                      ·
                        rfl

theorem cell23_2306595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_2306595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306595 prefixEnd_2306595 := by exact prefixLift 2306595
  have htrace : WordTrace (prefixWord ++ tailWord_2306595) baseStart_2306595 baseEnd_2306595 := by
    simpa [prefixWord, tailWord_2306595, baseEnd_2306595] using wordTrace_append hprefix tailTrace_2306595
  have hstable : (prefixWord ++ tailWord_2306595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306595).length < 2 ^ (prefixWord ++ tailWord_2306595).sum := by decide
  have hdescent : baseEnd_2306595 < baseStart_2306595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306602 : List Nat := [3, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_2306602 : Nat := 118140960795 + 2306602 * 2 ^ 59
def prefixEnd_2306602 : Nat := 4983230072969 + 3 ^ 40 * 2306602 * 2
def baseEnd_2306602 : Nat := 1184395504622089642767137

theorem tailTrace_2306602 : CollatzResearch.WordTrace tailWord_2306602 prefixEnd_2306602 1184395504622089642767137 := by
  unfold tailWord_2306602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21032171597395591275960515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56085790926388243402561373 21032171597395591275960515)
  ·
    refine ⟨31548257396093386913940773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21032171597395591275960515 31548257396093386913940773)
    ·
      refine ⟨5915298261767510046363895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31548257396093386913940773 5915298261767510046363895)
      ·
        refine ⟨8872947392651265069545843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915298261767510046363895 8872947392651265069545843)
        ·
          refine ⟨13309421088976897604318765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8872947392651265069545843 13309421088976897604318765)
          ·
            refine ⟨4991032908366336601619537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13309421088976897604318765 4991032908366336601619537)
            ·
              refine ⟨3743274681274752451214653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4991032908366336601619537 3743274681274752451214653)
              ·
                refine ⟨1403728005478032169205495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3743274681274752451214653 1403728005478032169205495)
                ·
                  refine ⟨2105592008217048253808243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403728005478032169205495 2105592008217048253808243)
                  ·
                    refine ⟨3158388012325572380712365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2105592008217048253808243 3158388012325572380712365)
                    ·
                      refine ⟨1184395504622089642767137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3158388012325572380712365 1184395504622089642767137)
                      ·
                        rfl

theorem cell23_2306602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_2306602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306602 prefixEnd_2306602 := by exact prefixLift 2306602
  have htrace : WordTrace (prefixWord ++ tailWord_2306602) baseStart_2306602 baseEnd_2306602 := by
    simpa [prefixWord, tailWord_2306602, baseEnd_2306602] using wordTrace_append hprefix tailTrace_2306602
  have hstable : (prefixWord ++ tailWord_2306602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306602).length < 2 ^ (prefixWord ++ tailWord_2306602).sum := by decide
  have hdescent : baseEnd_2306602 < baseStart_2306602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306608 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 1, 1, 4]
def baseStart_2306608 : Nat := 118140960795 + 2306608 * 2 ^ 59
def prefixEnd_2306608 : Nat := 4983230072969 + 3 ^ 40 * 2306608 * 2
def baseEnd_2306608 : Nat := 1184398585506016619292109

theorem tailTrace_2306608 : CollatzResearch.WordTrace tailWord_2306608 prefixEnd_2306608 1184398585506016619292109 := by
  unfold tailWord_2306608
  simp only [CollatzResearch.WordTrace]
  refine ⟨42064452613780314064280239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56085936818373752085706985 42064452613780314064280239)
  ·
    refine ⟨63096678920670471096420359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42064452613780314064280239 63096678920670471096420359)
    ·
      refine ⟨94645018381005706644630539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63096678920670471096420359 94645018381005706644630539)
      ·
        refine ⟨141967527571508559966945809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94645018381005706644630539 141967527571508559966945809)
        ·
          refine ⟨106475645678631419975209357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141967527571508559966945809 106475645678631419975209357)
          ·
            refine ⟨39928367129486782490703509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106475645678631419975209357 39928367129486782490703509)
            ·
              refine ⟨1871642209194692929251727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39928367129486782490703509 1871642209194692929251727)
              ·
                refine ⟨2807463313792039393877591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871642209194692929251727 2807463313792039393877591)
                ·
                  refine ⟨4211194970688059090816387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807463313792039393877591 4211194970688059090816387)
                  ·
                    refine ⟨6316792456032088636224581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4211194970688059090816387 6316792456032088636224581)
                    ·
                      refine ⟨1184398585506016619292109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6316792456032088636224581 1184398585506016619292109)
                      ·
                        rfl

theorem cell23_2306608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 1, 4].length) (baseStart_2306608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306608 prefixEnd_2306608 := by exact prefixLift 2306608
  have htrace : WordTrace (prefixWord ++ tailWord_2306608) baseStart_2306608 baseEnd_2306608 := by
    simpa [prefixWord, tailWord_2306608, baseEnd_2306608] using wordTrace_append hprefix tailTrace_2306608
  have hstable : (prefixWord ++ tailWord_2306608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306608).length < 2 ^ (prefixWord ++ tailWord_2306608).sum := by decide
  have hdescent : baseEnd_2306608 < baseStart_2306608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306618 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_2306618 : Nat := 118140960795 + 2306618 * 2 ^ 59
def prefixEnd_2306618 : Nat := 4983230072969 + 3 ^ 40 * 2306618 * 2
def baseEnd_2306618 : Nat := 394801240104187193389021

theorem tailTrace_2306618 : CollatzResearch.WordTrace tailWord_2306618 prefixEnd_2306618 394801240104187193389021 := by
  unfold tailWord_2306618
  simp only [CollatzResearch.WordTrace]
  refine ⟨21032317489381099959106127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56086179971682933224283005 21032317489381099959106127)
  ·
    refine ⟨31548476234071649938659191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21032317489381099959106127 31548476234071649938659191)
    ·
      refine ⟨47322714351107474907988787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31548476234071649938659191 47322714351107474907988787)
      ·
        refine ⟨70984071526661212361983181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47322714351107474907988787 70984071526661212361983181)
        ·
          refine ⟨26619026822497954635743693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70984071526661212361983181 26619026822497954635743693)
          ·
            refine ⟨9982135058436732988403885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26619026822497954635743693 9982135058436732988403885)
            ·
              refine ⟨3743300646913774870651457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9982135058436732988403885 3743300646913774870651457)
              ·
                refine ⟨2807475485185331152988593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3743300646913774870651457 2807475485185331152988593)
                ·
                  refine ⟨2105606613888998364741445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2807475485185331152988593 2105606613888998364741445)
                  ·
                    refine ⟨394801240104187193389021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2105606613888998364741445 394801240104187193389021)
                    ·
                      rfl

theorem cell23_2306618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_2306618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306618 prefixEnd_2306618 := by exact prefixLift 2306618
  have htrace : WordTrace (prefixWord ++ tailWord_2306618) baseStart_2306618 baseEnd_2306618 := by
    simpa [prefixWord, tailWord_2306618, baseEnd_2306618] using wordTrace_append hprefix tailTrace_2306618
  have hstable : (prefixWord ++ tailWord_2306618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306618).length < 2 ^ (prefixWord ++ tailWord_2306618).sum := by decide
  have hdescent : baseEnd_2306618 < baseStart_2306618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306625 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2306625 : Nat := 118140960795 + 2306625 * 2 ^ 59
def prefixEnd_2306625 : Nat := 4983230072969 + 3 ^ 40 * 2306625 * 2
def baseEnd_2306625 : Nat := 1184407314677143052779531

theorem tailTrace_2306625 : CollatzResearch.WordTrace tailWord_2306625 prefixEnd_2306625 1184407314677143052779531 := by
  unfold tailWord_2306625
  simp only [CollatzResearch.WordTrace]
  refine ⟨84129525268499040031929329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56086350178999360021286219 84129525268499040031929329)
  ·
    refine ⟨63097143951374280023946997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84129525268499040031929329 63097143951374280023946997)
    ·
      refine ⟨5915357245441338752245031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63097143951374280023946997 5915357245441338752245031)
      ·
        refine ⟨8873035868162008128367547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915357245441338752245031 8873035868162008128367547)
        ·
          refine ⟨13309553802243012192551321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8873035868162008128367547 13309553802243012192551321)
          ·
            refine ⟨9982165351682259144413491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13309553802243012192551321 9982165351682259144413491)
            ·
              refine ⟨14973248027523388716620237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9982165351682259144413491 14973248027523388716620237)
              ·
                refine ⟨5614968010321270768732589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14973248027523388716620237 5614968010321270768732589)
                ·
                  refine ⟨2105613003870476538274721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5614968010321270768732589 2105613003870476538274721)
                  ·
                    refine ⟨1579209752902857403706041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105613003870476538274721 1579209752902857403706041)
                    ·
                      refine ⟨1184407314677143052779531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579209752902857403706041 1184407314677143052779531)
                      ·
                        rfl

theorem cell23_2306625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2306625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306625 prefixEnd_2306625 := by exact prefixLift 2306625
  have htrace : WordTrace (prefixWord ++ tailWord_2306625) baseStart_2306625 baseEnd_2306625 := by
    simpa [prefixWord, tailWord_2306625, baseEnd_2306625] using wordTrace_append hprefix tailTrace_2306625
  have hstable : (prefixWord ++ tailWord_2306625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306625).length < 2 ^ (prefixWord ++ tailWord_2306625).sum := by decide
  have hdescent : baseEnd_2306625 < baseStart_2306625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306692 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_2306692 : Nat := 118140960795 + 2306692 * 2 ^ 59
def prefixEnd_2306692 : Nat := 4983230072969 + 3 ^ 40 * 2306692 * 2
def baseEnd_2306692 : Nat := 1184441717880994290641723

theorem tailTrace_2306692 : CollatzResearch.WordTrace tailWord_2306692 prefixEnd_2306692 1184441717880994290641723 := by
  unfold tailWord_2306692
  simp only [CollatzResearch.WordTrace]
  refine ⟨42065984479628155237309165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56087979306170873649745553 42065984479628155237309165)
  ·
    refine ⟨15774744179860558213990937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42065984479628155237309165 15774744179860558213990937)
    ·
      refine ⟨11831058134895418660493203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15774744179860558213990937 11831058134895418660493203)
      ·
        refine ⟨17746587202343127990739805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11831058134895418660493203 17746587202343127990739805)
        ·
          refine ⟨6654970200878672996527427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17746587202343127990739805 6654970200878672996527427)
          ·
            refine ⟨9982455301318009494791141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6654970200878672996527427 9982455301318009494791141)
            ·
              refine ⟨1871710368997126780273339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9982455301318009494791141 1871710368997126780273339)
              ·
                refine ⟨2807565553495690170410009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871710368997126780273339 2807565553495690170410009)
                ·
                  refine ⟨2105674165121767627807507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2807565553495690170410009 2105674165121767627807507)
                  ·
                    refine ⟨3158511247682651441711261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2105674165121767627807507 3158511247682651441711261)
                    ·
                      refine ⟨1184441717880994290641723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3158511247682651441711261 1184441717880994290641723)
                      ·
                        rfl

theorem cell23_2306692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_2306692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306692 prefixEnd_2306692 := by exact prefixLift 2306692
  have htrace : WordTrace (prefixWord ++ tailWord_2306692) baseStart_2306692 baseEnd_2306692 := by
    simpa [prefixWord, tailWord_2306692, baseEnd_2306692] using wordTrace_append hprefix tailTrace_2306692
  have hstable : (prefixWord ++ tailWord_2306692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306692).length < 2 ^ (prefixWord ++ tailWord_2306692).sum := by decide
  have hdescent : baseEnd_2306692 < baseStart_2306692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306718 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2306718 : Nat := 118140960795 + 2306718 * 2 ^ 59
def prefixEnd_2306718 : Nat := 4983230072969 + 3 ^ 40 * 2306718 * 2
def baseEnd_2306718 : Nat := 1184455068378011188916603

theorem tailTrace_2306718 : CollatzResearch.WordTrace tailWord_2306718 prefixEnd_2306718 1184455068378011188916603 := by
  unfold tailWord_2306718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10516614657145264614383101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56088611504774744610043205 10516614657145264614383101)
  ·
    refine ⟨3943730496429474230393663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10516614657145264614383101 3943730496429474230393663)
    ·
      refine ⟨5915595744644211345590495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3943730496429474230393663 5915595744644211345590495)
      ·
        refine ⟨8873393616966317018385743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915595744644211345590495 8873393616966317018385743)
        ·
          refine ⟨13310090425449475527578615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8873393616966317018385743 13310090425449475527578615)
          ·
            refine ⟨19965135638174213291367923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13310090425449475527578615 19965135638174213291367923)
            ·
              refine ⟨29947703457261319937051885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19965135638174213291367923 29947703457261319937051885)
              ·
                refine ⟨11230388796472994976394457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29947703457261319937051885 11230388796472994976394457)
                ·
                  refine ⟨8422791597354746232295843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11230388796472994976394457 8422791597354746232295843)
                  ·
                    refine ⟨12634187396032119348443765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8422791597354746232295843 12634187396032119348443765)
                    ·
                      refine ⟨1184455068378011188916603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12634187396032119348443765 1184455068378011188916603)
                      ·
                        rfl

theorem cell23_2306718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2306718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306718 prefixEnd_2306718 := by exact prefixLift 2306718
  have htrace : WordTrace (prefixWord ++ tailWord_2306718) baseStart_2306718 baseEnd_2306718 := by
    simpa [prefixWord, tailWord_2306718, baseEnd_2306718] using wordTrace_append hprefix tailTrace_2306718
  have hstable : (prefixWord ++ tailWord_2306718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306718).length < 2 ^ (prefixWord ++ tailWord_2306718).sum := by decide
  have hdescent : baseEnd_2306718 < baseStart_2306718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306748 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_2306748 : Nat := 118140960795 + 2306748 * 2 ^ 59
def prefixEnd_2306748 : Nat := 4983230072969 + 3 ^ 40 * 2306748 * 2
def baseEnd_2306748 : Nat := 1184470472797646071541465

theorem tailTrace_2306748 : CollatzResearch.WordTrace tailWord_2306748 prefixEnd_2306748 1184470472797646071541465 := by
  unfold tailWord_2306748
  simp only [CollatzResearch.WordTrace]
  refine ⟨42067005723526716019328449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56089340964702288025771265 42067005723526716019328449)
  ·
    refine ⟨31550254292645037014496337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42067005723526716019328449 31550254292645037014496337)
    ·
      refine ⟨23662690719483777760872253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31550254292645037014496337 23662690719483777760872253)
      ·
        refine ⟨8873509019806416660327095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23662690719483777760872253 8873509019806416660327095)
        ·
          refine ⟨13310263529709624990490643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8873509019806416660327095 13310263529709624990490643)
          ·
            refine ⟨19965395294564437485735965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13310263529709624990490643 19965395294564437485735965)
            ·
              refine ⟨7487023235461664057150987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19965395294564437485735965 7487023235461664057150987)
              ·
                refine ⟨11230534853192496085726481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7487023235461664057150987 11230534853192496085726481)
                ·
                  refine ⟨8422901139894372064294861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11230534853192496085726481 8422901139894372064294861)
                  ·
                    refine ⟨3158587927460389524110573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8422901139894372064294861 3158587927460389524110573)
                    ·
                      refine ⟨1184470472797646071541465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3158587927460389524110573 1184470472797646071541465)
                      ·
                        rfl

theorem cell23_2306748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_2306748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306748 prefixEnd_2306748 := by exact prefixLift 2306748
  have htrace : WordTrace (prefixWord ++ tailWord_2306748) baseStart_2306748 baseEnd_2306748 := by
    simpa [prefixWord, tailWord_2306748, baseEnd_2306748] using wordTrace_append hprefix tailTrace_2306748
  have hstable : (prefixWord ++ tailWord_2306748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306748).length < 2 ^ (prefixWord ++ tailWord_2306748).sum := by decide
  have hdescent : baseEnd_2306748 < baseStart_2306748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306772 : List Nat := [2, 4, 1, 3, 2, 1, 2, 3, 5]
def baseStart_2306772 : Nat := 118140960795 + 2306772 * 2 ^ 59
def prefixEnd_2306772 : Nat := 4983230072969 + 3 ^ 40 * 2306772 * 2
def baseEnd_2306772 : Nat := 131609199592594886404595

theorem tailTrace_2306772 : CollatzResearch.WordTrace tailWord_2306772 prefixEnd_2306772 131609199592594886404595 := by
  unfold tailWord_2306772
  simp only [CollatzResearch.WordTrace]
  refine ⟨42067443399483242068765285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56089924532644322758353713 42067443399483242068765285)
  ·
    refine ⟨7887645637403107887893491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42067443399483242068765285 7887645637403107887893491)
    ·
      refine ⟨11831468456104661831840237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7887645637403107887893491 11831468456104661831840237)
      ·
        refine ⟨4436800671039248186940089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11831468456104661831840237 4436800671039248186940089)
        ·
          refine ⟨3327600503279436140205067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4436800671039248186940089 3327600503279436140205067)
          ·
            refine ⟨4991400754919154210307601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327600503279436140205067 4991400754919154210307601)
            ·
              refine ⟨3743550566189365657730701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4991400754919154210307601 3743550566189365657730701)
              ·
                refine ⟨1403831462321012121649013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3743550566189365657730701 1403831462321012121649013)
                ·
                  refine ⟨131609199592594886404595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1403831462321012121649013 131609199592594886404595)
                  ·
                    rfl

theorem cell23_2306772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_2306772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306772 prefixEnd_2306772 := by exact prefixLift 2306772
  have htrace : WordTrace (prefixWord ++ tailWord_2306772) baseStart_2306772 baseEnd_2306772 := by
    simpa [prefixWord, tailWord_2306772, baseEnd_2306772] using wordTrace_append hprefix tailTrace_2306772
  have hstable : (prefixWord ++ tailWord_2306772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306772).length < 2 ^ (prefixWord ++ tailWord_2306772).sum := by decide
  have hdescent : baseEnd_2306772 < baseStart_2306772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306801 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_2306801 : Nat := 118140960795 + 2306801 * 2 ^ 59
def prefixEnd_2306801 : Nat := 4983230072969 + 3 ^ 40 * 2306801 * 2
def baseEnd_2306801 : Nat := 1184497687272334364178721

theorem tailTrace_2306801 : CollatzResearch.WordTrace tailWord_2306801 prefixEnd_2306801 1184497687272334364178721 := by
  unfold tailWord_2306801
  simp only [CollatzResearch.WordTrace]
  refine ⟨84135944515861422090336257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56090629677240948060224171 84135944515861422090336257)
  ·
    refine ⟨63101958386896066567752193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84135944515861422090336257 63101958386896066567752193)
    ·
      refine ⟨47326468790172049925814145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63101958386896066567752193 47326468790172049925814145)
      ·
        refine ⟨35494851592629037444360609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47326468790172049925814145 35494851592629037444360609)
        ·
          refine ⟨26621138694471778083270457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35494851592629037444360609 26621138694471778083270457)
          ·
            refine ⟨19965854020853833562452843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26621138694471778083270457 19965854020853833562452843)
            ·
              refine ⟨29948781031280750343679265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19965854020853833562452843 29948781031280750343679265)
              ·
                refine ⟨22461585773460562757759449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29948781031280750343679265 22461585773460562757759449)
                ·
                  refine ⟨16846189330095422068319587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22461585773460562757759449 16846189330095422068319587)
                  ·
                    refine ⟨25269283995143133102479381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16846189330095422068319587 25269283995143133102479381)
                    ·
                      refine ⟨1184497687272334364178721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25269283995143133102479381 1184497687272334364178721)
                      ·
                        rfl

theorem cell23_2306801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_2306801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306801 prefixEnd_2306801 := by exact prefixLift 2306801
  have htrace : WordTrace (prefixWord ++ tailWord_2306801) baseStart_2306801 baseEnd_2306801 := by
    simpa [prefixWord, tailWord_2306801, baseEnd_2306801] using wordTrace_append hprefix tailTrace_2306801
  have hstable : (prefixWord ++ tailWord_2306801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306801).length < 2 ^ (prefixWord ++ tailWord_2306801).sum := by decide
  have hdescent : baseEnd_2306801 < baseStart_2306801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306851 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2306851 : Nat := 118140960795 + 2306851 * 2 ^ 59
def prefixEnd_2306851 : Nat := 4983230072969 + 3 ^ 40 * 2306851 * 2
def baseEnd_2306851 : Nat := 1184523361305059168553491

theorem tailTrace_2306851 : CollatzResearch.WordTrace tailWord_2306851 prefixEnd_2306851 1184523361305059168553491 := by
  unfold tailWord_2306851
  simp only [CollatzResearch.WordTrace]
  refine ⟨84137768165680280629656407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56091845443786853753104271 84137768165680280629656407)
  ·
    refine ⟨126206652248520420944484611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84137768165680280629656407 126206652248520420944484611)
    ·
      refine ⟨189309978372780631416726917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126206652248520420944484611 189309978372780631416726917)
      ·
        refine ⟨35495620944896368390636297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189309978372780631416726917 35495620944896368390636297)
        ·
          refine ⟨26621715708672276292977223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35495620944896368390636297 26621715708672276292977223)
          ·
            refine ⟨39932573563008414439465835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26621715708672276292977223 39932573563008414439465835)
            ·
              refine ⟨59898860344512621659198753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39932573563008414439465835 59898860344512621659198753)
              ·
                refine ⟨44924145258384466244399065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59898860344512621659198753 44924145258384466244399065)
                ·
                  refine ⟨33693108943788349683299299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44924145258384466244399065 33693108943788349683299299)
                  ·
                    refine ⟨50539663415682524524948949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33693108943788349683299299 50539663415682524524948949)
                    ·
                      refine ⟨1184523361305059168553491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50539663415682524524948949 1184523361305059168553491)
                      ·
                        rfl

theorem cell23_2306851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2306851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306851 prefixEnd_2306851 := by exact prefixLift 2306851
  have htrace : WordTrace (prefixWord ++ tailWord_2306851) baseStart_2306851 baseEnd_2306851 := by
    simpa [prefixWord, tailWord_2306851, baseEnd_2306851] using wordTrace_append hprefix tailTrace_2306851
  have hstable : (prefixWord ++ tailWord_2306851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306851).length < 2 ^ (prefixWord ++ tailWord_2306851).sum := by decide
  have hdescent : baseEnd_2306851 < baseStart_2306851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306862 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_2306862 : Nat := 118140960795 + 2306862 * 2 ^ 59
def prefixEnd_2306862 : Nat := 4983230072969 + 3 ^ 40 * 2306862 * 2
def baseEnd_2306862 : Nat := 131614334399139847279549

theorem tailTrace_2306862 : CollatzResearch.WordTrace tailWord_2306862 prefixEnd_2306862 131614334399139847279549 := by
  unfold tailWord_2306862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517271171080053688538355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56092112912426953005537893 10517271171080053688538355)
  ·
    refine ⟨15775906756620080532807533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10517271171080053688538355 15775906756620080532807533)
    ·
      refine ⟨5915965033732530199802825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15775906756620080532807533 5915965033732530199802825)
      ·
        refine ⟨4436973775299397649852119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5915965033732530199802825 4436973775299397649852119)
        ·
          refine ⟨6655460662949096474778179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4436973775299397649852119 6655460662949096474778179)
          ·
            refine ⟨9983190994423644712167269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655460662949096474778179 9983190994423644712167269)
            ·
              refine ⟨1871848311454433383531363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9983190994423644712167269 1871848311454433383531363)
              ·
                refine ⟨2807772467181650075297045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871848311454433383531363 2807772467181650075297045)
                ·
                  refine ⟨131614334399139847279549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2807772467181650075297045 131614334399139847279549)
                  ·
                    rfl

theorem cell23_2306862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_2306862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306862 prefixEnd_2306862 := by exact prefixLift 2306862
  have htrace : WordTrace (prefixWord ++ tailWord_2306862) baseStart_2306862 baseEnd_2306862 := by
    simpa [prefixWord, tailWord_2306862, baseEnd_2306862] using wordTrace_append hprefix tailTrace_2306862
  have hstable : (prefixWord ++ tailWord_2306862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306862).length < 2 ^ (prefixWord ++ tailWord_2306862).sum := by decide
  have hdescent : baseEnd_2306862 < baseStart_2306862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306865 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 4, 3, 2]
def baseStart_2306865 : Nat := 118140960795 + 2306865 * 2 ^ 59
def prefixEnd_2306865 : Nat := 4983230072969 + 3 ^ 40 * 2306865 * 2
def baseEnd_2306865 : Nat := 1184530550034222113778427

theorem tailTrace_2306865 : CollatzResearch.WordTrace tailWord_2306865 prefixEnd_2306865 1184530550034222113778427 := by
  unfold tailWord_2306865
  simp only [CollatzResearch.WordTrace]
  refine ⟨84138278787629561020666049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56092185858419707347110699 84138278787629561020666049)
  ·
    refine ⟨63103709090722170765499537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84138278787629561020666049 63103709090722170765499537)
    ·
      refine ⟨47327781818041628074124653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63103709090722170765499537 47327781818041628074124653)
      ·
        refine ⟨17747918181765610527796745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47327781818041628074124653 17747918181765610527796745)
        ·
          refine ⟨13310938636324207895847559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17747918181765610527796745 13310938636324207895847559)
          ·
            refine ⟨19966407954486311843771339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13310938636324207895847559 19966407954486311843771339)
            ·
              refine ⟨29949611931729467765657009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19966407954486311843771339 29949611931729467765657009)
              ·
                refine ⟨22462208948797100824242757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29949611931729467765657009 22462208948797100824242757)
                ·
                  refine ⟨4211664177899456404545517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22462208948797100824242757 4211664177899456404545517)
                  ·
                    refine ⟨1579374066712296151704569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4211664177899456404545517 1579374066712296151704569)
                    ·
                      refine ⟨1184530550034222113778427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579374066712296151704569 1184530550034222113778427)
                      ·
                        rfl

theorem cell23_2306865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_2306865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306865 prefixEnd_2306865 := by exact prefixLift 2306865
  have htrace : WordTrace (prefixWord ++ tailWord_2306865) baseStart_2306865 baseEnd_2306865 := by
    simpa [prefixWord, tailWord_2306865, baseEnd_2306865] using wordTrace_append hprefix tailTrace_2306865
  have hstable : (prefixWord ++ tailWord_2306865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306865).length < 2 ^ (prefixWord ++ tailWord_2306865).sum := by decide
  have hdescent : baseEnd_2306865 < baseStart_2306865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306888 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 1, 6]
def baseStart_2306888 : Nat := 118140960795 + 2306888 * 2 ^ 59
def prefixEnd_2306888 : Nat := 4983230072969 + 3 ^ 40 * 2306888 * 2
def baseEnd_2306888 : Nat := 394847453363091841263607

theorem tailTrace_2306888 : CollatzResearch.WordTrace tailWord_2306888 prefixEnd_2306888 394847453363091841263607 := by
  unfold tailWord_2306888
  simp only [CollatzResearch.WordTrace]
  refine ⟨42069558833273117974376659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56092745111030823965835545 42069558833273117974376659)
  ·
    refine ⟨63104338249909676961564989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42069558833273117974376659 63104338249909676961564989)
    ·
      refine ⟨23664126843716128860586871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63104338249909676961564989 23664126843716128860586871)
      ·
        refine ⟨35496190265574193290880307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23664126843716128860586871 35496190265574193290880307)
        ·
          refine ⟨53244285398361289936320461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35496190265574193290880307 53244285398361289936320461)
          ·
            refine ⟨19966607024385483726120173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53244285398361289936320461 19966607024385483726120173)
            ·
              refine ⟨7487477634144556397295065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19966607024385483726120173 7487477634144556397295065)
              ·
                refine ⟨5615608225608417297971299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7487477634144556397295065 5615608225608417297971299)
                ·
                  refine ⟨8423412338412625946956949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5615608225608417297971299 8423412338412625946956949)
                  ·
                    refine ⟨394847453363091841263607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8423412338412625946956949 394847453363091841263607)
                    ·
                      rfl

theorem cell23_2306888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_2306888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306888 prefixEnd_2306888 := by exact prefixLift 2306888
  have htrace : WordTrace (prefixWord ++ tailWord_2306888) baseStart_2306888 baseEnd_2306888 := by
    simpa [prefixWord, tailWord_2306888, baseEnd_2306888] using wordTrace_append hprefix tailTrace_2306888
  have hstable : (prefixWord ++ tailWord_2306888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306888).length < 2 ^ (prefixWord ++ tailWord_2306888).sum := by decide
  have hdescent : baseEnd_2306888 < baseStart_2306888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306891 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 6]
def baseStart_2306891 : Nat := 118140960795 + 2306891 * 2 ^ 59
def prefixEnd_2306891 : Nat := 4983230072969 + 3 ^ 40 * 2306891 * 2
def baseEnd_2306891 : Nat := 1184543900531239012053307

theorem tailTrace_2306891 : CollatzResearch.WordTrace tailWord_2306891 prefixEnd_2306891 1184543900531239012053307 := by
  unfold tailWord_2306891
  simp only [CollatzResearch.WordTrace]
  refine ⟨84139227085535367461112527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56092818057023578307408351 84139227085535367461112527)
  ·
    refine ⟨126208840628303051191668791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84139227085535367461112527 126208840628303051191668791)
    ·
      refine ⟨189313260942454576787503187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126208840628303051191668791 189313260942454576787503187)
      ·
        refine ⟨283969891413681865181254781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189313260942454576787503187 283969891413681865181254781)
        ·
          refine ⟨106488709280130699442970543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283969891413681865181254781 106488709280130699442970543)
          ·
            refine ⟨159733063920196049164455815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106488709280130699442970543 159733063920196049164455815)
            ·
              refine ⟨239599595880294073746683723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159733063920196049164455815 239599595880294073746683723)
              ·
                refine ⟨359399393820441110620025585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239599595880294073746683723 359399393820441110620025585)
                ·
                  refine ⟨269549545365330832965019189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359399393820441110620025585 269549545365330832965019189)
                  ·
                    refine ⟨25270269877999765590470549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 269549545365330832965019189 25270269877999765590470549)
                    ·
                      refine ⟨1184543900531239012053307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25270269877999765590470549 1184543900531239012053307)
                      ·
                        rfl

theorem cell23_2306891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_2306891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306891 prefixEnd_2306891 := by exact prefixLift 2306891
  have htrace : WordTrace (prefixWord ++ tailWord_2306891) baseStart_2306891 baseEnd_2306891 := by
    simpa [prefixWord, tailWord_2306891, baseEnd_2306891] using wordTrace_append hprefix tailTrace_2306891
  have hstable : (prefixWord ++ tailWord_2306891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306891).length < 2 ^ (prefixWord ++ tailWord_2306891).sum := by decide
  have hdescent : baseEnd_2306891 < baseStart_2306891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306892 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_2306892 : Nat := 118140960795 + 2306892 * 2 ^ 59
def prefixEnd_2306892 : Nat := 4983230072969 + 3 ^ 40 * 2306892 * 2
def baseEnd_2306892 : Nat := 394848138003964502713601

theorem tailTrace_2306892 : CollatzResearch.WordTrace tailWord_2306892 prefixEnd_2306892 394848138003964502713601 := by
  unfold tailWord_2306892
  simp only [CollatzResearch.WordTrace]
  refine ⟨42069631779265872315949465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56092842372354496421265953 42069631779265872315949465)
  ·
    refine ⟨31552223834449404236962099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42069631779265872315949465 31552223834449404236962099)
    ·
      refine ⟨47328335751674106355443149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31552223834449404236962099 47328335751674106355443149)
      ·
        refine ⟨17748125906877789883291181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47328335751674106355443149 17748125906877789883291181)
        ·
          refine ⟨6655547215079171206234193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17748125906877789883291181 6655547215079171206234193)
          ·
            refine ⟨4991660411309378404675645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6655547215079171206234193 4991660411309378404675645)
            ·
              refine ⟨1871872654241016901753367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4991660411309378404675645 1871872654241016901753367)
              ·
                refine ⟨2807808981361525352630051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871872654241016901753367 2807808981361525352630051)
                ·
                  refine ⟨4211713472042288028945077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807808981361525352630051 4211713472042288028945077)
                  ·
                    refine ⟨394848138003964502713601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4211713472042288028945077 394848138003964502713601)
                    ·
                      rfl

theorem cell23_2306892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_2306892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306892 prefixEnd_2306892 := by exact prefixLift 2306892
  have htrace : WordTrace (prefixWord ++ tailWord_2306892) baseStart_2306892 baseEnd_2306892 := by
    simpa [prefixWord, tailWord_2306892, baseEnd_2306892] using wordTrace_append hprefix tailTrace_2306892
  have hstable : (prefixWord ++ tailWord_2306892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306892).length < 2 ^ (prefixWord ++ tailWord_2306892).sum := by decide
  have hdescent : baseEnd_2306892 < baseStart_2306892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306905 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 2, 4]
def baseStart_2306905 : Nat := 118140960795 + 2306905 * 2 ^ 59
def prefixEnd_2306905 : Nat := 4983230072969 + 3 ^ 40 * 2306905 * 2
def baseEnd_2306905 : Nat := 394850363086800652426081

theorem tailTrace_2306905 : CollatzResearch.WordTrace tailWord_2306905 prefixEnd_2306905 394850363086800652426081 := by
  unfold tailWord_2306905
  simp only [CollatzResearch.WordTrace]
  refine ⟨84139737707484647852122169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56093158471656431901414779 84139737707484647852122169)
  ·
    refine ⟨63104803280613485889091627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84139737707484647852122169 63104803280613485889091627)
    ·
      refine ⟨94657204920920228833637441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63104803280613485889091627 94657204920920228833637441)
      ·
        refine ⟨70992903690690171625228081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94657204920920228833637441 70992903690690171625228081)
        ·
          refine ⟨53244677768017628718921061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70992903690690171625228081 53244677768017628718921061)
          ·
            refine ⟨9983377081503305384797699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53244677768017628718921061 9983377081503305384797699)
            ·
              refine ⟨14975065622254958077196549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9983377081503305384797699 14975065622254958077196549)
              ·
                refine ⟨2807824804172804639474353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14975065622254958077196549 2807824804172804639474353)
                ·
                  refine ⟨2105868603129603479605765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2807824804172804639474353 2105868603129603479605765)
                  ·
                    refine ⟨394850363086800652426081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2105868603129603479605765 394850363086800652426081)
                    ·
                      rfl

theorem cell23_2306905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 4].length) (baseStart_2306905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306905 prefixEnd_2306905 := by exact prefixLift 2306905
  have htrace : WordTrace (prefixWord ++ tailWord_2306905) baseStart_2306905 baseEnd_2306905 := by
    simpa [prefixWord, tailWord_2306905, baseEnd_2306905] using wordTrace_append hprefix tailTrace_2306905
  have hstable : (prefixWord ++ tailWord_2306905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306905).length < 2 ^ (prefixWord ++ tailWord_2306905).sum := by decide
  have hdescent : baseEnd_2306905 < baseStart_2306905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306906 : List Nat := [3, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3]
def baseStart_2306906 : Nat := 118140960795 + 2306906 * 2 ^ 59
def prefixEnd_2306906 : Nat := 4983230072969 + 3 ^ 40 * 2306906 * 2
def baseEnd_2306906 : Nat := 1184551602741056453365739

theorem tailTrace_2306906 : CollatzResearch.WordTrace tailWord_2306906 prefixEnd_2306906 1184551602741056453365739 := by
  unfold tailWord_2306906
  simp only [CollatzResearch.WordTrace]
  refine ⟨21034943545120256255727143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56093182786987350015272381 21034943545120256255727143)
  ·
    refine ⟨31552415317680384383590715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21034943545120256255727143 31552415317680384383590715)
    ·
      refine ⟨47328622976520576575386073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31552415317680384383590715 47328622976520576575386073)
      ·
        refine ⟨35496467232390432431539555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47328622976520576575386073 35496467232390432431539555)
        ·
          refine ⟨53244700848585648647309333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35496467232390432431539555 53244700848585648647309333)
          ·
            refine ⟨2495845352277452280342625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53244700848585648647309333 2495845352277452280342625)
            ·
              refine ⟨1871884014208089210256969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2495845352277452280342625 1871884014208089210256969)
              ·
                refine ⟨1403913010656066907692727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871884014208089210256969 1403913010656066907692727)
                ·
                  refine ⟨2105869515984100361539091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403913010656066907692727 2105869515984100361539091)
                  ·
                    refine ⟨3158804273976150542308637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2105869515984100361539091 3158804273976150542308637)
                    ·
                      refine ⟨1184551602741056453365739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3158804273976150542308637 1184551602741056453365739)
                      ·
                        rfl

theorem cell23_2306906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_2306906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306906 prefixEnd_2306906 := by exact prefixLift 2306906
  have htrace : WordTrace (prefixWord ++ tailWord_2306906) baseStart_2306906 baseEnd_2306906 := by
    simpa [prefixWord, tailWord_2306906, baseEnd_2306906] using wordTrace_append hprefix tailTrace_2306906
  have hstable : (prefixWord ++ tailWord_2306906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306906).length < 2 ^ (prefixWord ++ tailWord_2306906).sum := by decide
  have hdescent : baseEnd_2306906 < baseStart_2306906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306912 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 3, 2, 2]
def baseStart_2306912 : Nat := 118140960795 + 2306912 * 2 ^ 59
def prefixEnd_2306912 : Nat := 4983230072969 + 3 ^ 40 * 2306912 * 2
def baseEnd_2306912 : Nat := 1184554683624983429890711

theorem tailTrace_2306912 : CollatzResearch.WordTrace tailWord_2306912 prefixEnd_2306912 1184554683624983429890711 := by
  unfold tailWord_2306912
  simp only [CollatzResearch.WordTrace]
  refine ⟨42069996509229644023813495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56093328678972858698417993 42069996509229644023813495)
  ·
    refine ⟨63104994763844466035720243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42069996509229644023813495 63104994763844466035720243)
    ·
      refine ⟨94657492145766699053580365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63104994763844466035720243 94657492145766699053580365)
      ·
        refine ⟨35496559554662512145092637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94657492145766699053580365 35496559554662512145092637)
        ·
          refine ⟨13311209832998442054409739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35496559554662512145092637 13311209832998442054409739)
          ·
            refine ⟨19966814749497663081614609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13311209832998442054409739 19966814749497663081614609)
            ·
              refine ⟨14975111062123247311210957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19966814749497663081614609 14975111062123247311210957)
              ·
                refine ⟨5615666648296217741704109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14975111062123247311210957 5615666648296217741704109)
                ·
                  refine ⟨2105874993111081653139041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5615666648296217741704109 2105874993111081653139041)
                  ·
                    refine ⟨1579406244833311239854281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105874993111081653139041 1579406244833311239854281)
                    ·
                      refine ⟨1184554683624983429890711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579406244833311239854281 1184554683624983429890711)
                      ·
                        rfl

theorem cell23_2306912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_2306912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306912 prefixEnd_2306912 := by exact prefixLift 2306912
  have htrace : WordTrace (prefixWord ++ tailWord_2306912) baseStart_2306912 baseEnd_2306912 := by
    simpa [prefixWord, tailWord_2306912, baseEnd_2306912] using wordTrace_append hprefix tailTrace_2306912
  have hstable : (prefixWord ++ tailWord_2306912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306912).length < 2 ^ (prefixWord ++ tailWord_2306912).sum := by decide
  have hdescent : baseEnd_2306912 < baseStart_2306912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306915 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 3]
def baseStart_2306915 : Nat := 118140960795 + 2306915 * 2 ^ 59
def prefixEnd_2306915 : Nat := 4983230072969 + 3 ^ 40 * 2306915 * 2
def baseEnd_2306915 : Nat := 1184556224066946918153197

theorem tailTrace_2306915 : CollatzResearch.WordTrace tailWord_2306915 prefixEnd_2306915 1184556224066946918153197 := by
  unfold tailWord_2306915
  simp only [CollatzResearch.WordTrace]
  refine ⟨84140102437448419559986199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56093401624965613039990799 84140102437448419559986199)
  ·
    refine ⟨126210153656172629339979299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84140102437448419559986199 126210153656172629339979299)
    ·
      refine ⟨189315230484258944009968949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126210153656172629339979299 189315230484258944009968949)
      ·
        refine ⟨17748302857899276000934589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189315230484258944009968949 17748302857899276000934589)
        ·
          refine ⟨6655613571712228500350471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17748302857899276000934589 6655613571712228500350471)
          ·
            refine ⟨9983420357568342750525707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655613571712228500350471 9983420357568342750525707)
            ·
              refine ⟨14975130536352514125788561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9983420357568342750525707 14975130536352514125788561)
              ·
                refine ⟨11231347902264385594341421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14975130536352514125788561 11231347902264385594341421)
                ·
                  refine ⟨4211755463349144597878033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11231347902264385594341421 4211755463349144597878033)
                  ·
                    refine ⟨3158816597511858448408525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4211755463349144597878033 3158816597511858448408525)
                    ·
                      refine ⟨1184556224066946918153197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3158816597511858448408525 1184556224066946918153197)
                      ·
                        rfl

theorem cell23_2306915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_2306915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306915 prefixEnd_2306915 := by exact prefixLift 2306915
  have htrace : WordTrace (prefixWord ++ tailWord_2306915) baseStart_2306915 baseEnd_2306915 := by
    simpa [prefixWord, tailWord_2306915, baseEnd_2306915] using wordTrace_append hprefix tailTrace_2306915
  have hstable : (prefixWord ++ tailWord_2306915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306915).length < 2 ^ (prefixWord ++ tailWord_2306915).sum := by decide
  have hdescent : baseEnd_2306915 < baseStart_2306915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306946 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2306946 : Nat := 118140960795 + 2306946 * 2 ^ 59
def prefixEnd_2306946 : Nat := 4983230072969 + 3 ^ 40 * 2306946 * 2
def baseEnd_2306946 : Nat := 1184572141967236296865555

theorem tailTrace_2306946 : CollatzResearch.WordTrace tailWord_2306946 prefixEnd_2306946 1184572141967236296865555 := by
  unfold tailWord_2306946
  simp only [CollatzResearch.WordTrace]
  refine ⟨21035308275084027963591173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56094155400224074569576461 21035308275084027963591173)
  ·
    refine ⟨3944120301578255243173345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21035308275084027963591173 3944120301578255243173345)
    ·
      refine ⟨2958090226183691432380009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3944120301578255243173345 2958090226183691432380009)
      ·
        refine ⟨2218567669637768574285007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2958090226183691432380009 2218567669637768574285007)
        ·
          refine ⟨3327851504456652861427511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218567669637768574285007 3327851504456652861427511)
          ·
            refine ⟨4991777256684979292141267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327851504456652861427511 4991777256684979292141267)
            ·
              refine ⟨7487665885027468938211901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991777256684979292141267 7487665885027468938211901)
              ·
                refine ⟨2807874706885300851829463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7487665885027468938211901 2807874706885300851829463)
                ·
                  refine ⟨4211812060327951277744195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807874706885300851829463 4211812060327951277744195)
                  ·
                    refine ⟨6317718090491926916616293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4211812060327951277744195 6317718090491926916616293)
                    ·
                      refine ⟨1184572141967236296865555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6317718090491926916616293 1184572141967236296865555)
                      ·
                        rfl

theorem cell23_2306946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2306946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306946 prefixEnd_2306946 := by exact prefixLift 2306946
  have htrace : WordTrace (prefixWord ++ tailWord_2306946) baseStart_2306946 baseEnd_2306946 := by
    simpa [prefixWord, tailWord_2306946, baseEnd_2306946] using wordTrace_append hprefix tailTrace_2306946
  have hstable : (prefixWord ++ tailWord_2306946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306946).length < 2 ^ (prefixWord ++ tailWord_2306946).sum := by decide
  have hdescent : baseEnd_2306946 < baseStart_2306946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306949 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 1, 2, 3]
def baseStart_2306949 : Nat := 118140960795 + 2306949 * 2 ^ 59
def prefixEnd_2306949 : Nat := 4983230072969 + 3 ^ 40 * 2306949 * 2
def baseEnd_2306949 : Nat := 1184573682409199785128041

theorem tailTrace_2306949 : CollatzResearch.WordTrace tailWord_2306949 prefixEnd_2306949 1184573682409199785128041 := by
  unfold tailWord_2306949
  simp only [CollatzResearch.WordTrace]
  refine ⟨84141342519325243366723901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56094228346216828911149267 84141342519325243366723901)
  ·
    refine ⟨31553003444746966262521463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84141342519325243366723901 31553003444746966262521463)
    ·
      refine ⟨47329505167120449393782195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31553003444746966262521463 47329505167120449393782195)
      ·
        refine ⟨70994257750680674090673293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47329505167120449393782195 70994257750680674090673293)
        ·
          refine ⟨26622846656505252784002485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70994257750680674090673293 26622846656505252784002485)
          ·
            refine ⟨2495891874047367448500233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26622846656505252784002485 2495891874047367448500233)
            ·
              refine ⟨1871918905535525586375175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2495891874047367448500233 1871918905535525586375175)
              ·
                refine ⟨2807878358303288379562763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871918905535525586375175 2807878358303288379562763)
                ·
                  refine ⟨4211817537454932569344145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807878358303288379562763 4211817537454932569344145)
                  ·
                    refine ⟨3158863153091199427008109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4211817537454932569344145 3158863153091199427008109)
                    ·
                      refine ⟨1184573682409199785128041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3158863153091199427008109 1184573682409199785128041)
                      ·
                        rfl

theorem cell23_2306949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_2306949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306949 prefixEnd_2306949 := by exact prefixLift 2306949
  have htrace : WordTrace (prefixWord ++ tailWord_2306949) baseStart_2306949 baseEnd_2306949 := by
    simpa [prefixWord, tailWord_2306949, baseEnd_2306949] using wordTrace_append hprefix tailTrace_2306949
  have hstable : (prefixWord ++ tailWord_2306949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306949).length < 2 ^ (prefixWord ++ tailWord_2306949).sum := by decide
  have hdescent : baseEnd_2306949 < baseStart_2306949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306988 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_2306988 : Nat := 118140960795 + 2306988 * 2 ^ 59
def prefixEnd_2306988 : Nat := 4983230072969 + 3 ^ 40 * 2306988 * 2
def baseEnd_2306988 : Nat := 1184593708154725132540361

theorem tailTrace_2306988 : CollatzResearch.WordTrace tailWord_2306988 prefixEnd_2306988 1184593708154725132540361 := by
  unfold tailWord_2306988
  simp only [CollatzResearch.WordTrace]
  refine ⟨42071382483091976513696809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56095176644122635351595745 42071382483091976513696809)
  ·
    refine ⟨31553536862318982385272607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42071382483091976513696809 31553536862318982385272607)
    ·
      refine ⟨47330305293478473577908911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31553536862318982385272607 47330305293478473577908911)
      ·
        refine ⟨70995457940217710366863367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47330305293478473577908911 70995457940217710366863367)
        ·
          refine ⟨106493186910326565550295051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70995457940217710366863367 106493186910326565550295051)
          ·
            refine ⟨159739780365489848325442577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106493186910326565550295051 159739780365489848325442577)
            ·
              refine ⟨119804835274117386244081933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159739780365489848325442577 119804835274117386244081933)
              ·
                refine ⟨44926813227794019841530725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119804835274117386244081933 44926813227794019841530725)
                ·
                  refine ⟨8423777480211378720287011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44926813227794019841530725 8423777480211378720287011)
                  ·
                    refine ⟨12635666220317068080430517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8423777480211378720287011 12635666220317068080430517)
                    ·
                      refine ⟨1184593708154725132540361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12635666220317068080430517 1184593708154725132540361)
                      ·
                        rfl

theorem cell23_2306988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_2306988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2306988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2306988 prefixEnd_2306988 := by exact prefixLift 2306988
  have htrace : WordTrace (prefixWord ++ tailWord_2306988) baseStart_2306988 baseEnd_2306988 := by
    simpa [prefixWord, tailWord_2306988, baseEnd_2306988] using wordTrace_append hprefix tailTrace_2306988
  have hstable : (prefixWord ++ tailWord_2306988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306988).length < 2 ^ (prefixWord ++ tailWord_2306988).sum := by decide
  have hdescent : baseEnd_2306988 < baseStart_2306988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307002 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2]
def baseStart_2307002 : Nat := 118140960795 + 2307002 * 2 ^ 59
def prefixEnd_2307002 : Nat := 4983230072969 + 3 ^ 40 * 2307002 * 2
def baseEnd_2307002 : Nat := 1184600896883888077765297

theorem tailTrace_2307002 : CollatzResearch.WordTrace tailWord_2307002 prefixEnd_2307002 1184600896883888077765297 := by
  unfold tailWord_2307002
  simp only [CollatzResearch.WordTrace]
  refine ⟨21035818897033308354600815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56095517058755488945602173 21035818897033308354600815)
  ·
    refine ⟨31553728345549962531901223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21035818897033308354600815 31553728345549962531901223)
    ·
      refine ⟨47330592518324943797851835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31553728345549962531901223 47330592518324943797851835)
      ·
        refine ⟨70995888777487415696777753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47330592518324943797851835 70995888777487415696777753)
        ·
          refine ⟨53246916583115561772583315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70995888777487415696777753 53246916583115561772583315)
          ·
            refine ⟨79870374874673342658874973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53246916583115561772583315 79870374874673342658874973)
            ·
              refine ⟨29951390578002503497078115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79870374874673342658874973 29951390578002503497078115)
              ·
                refine ⟨44927085867003755245617173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29951390578002503497078115 44927085867003755245617173)
                ·
                  refine ⟨2105957150015801027138305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44927085867003755245617173 2105957150015801027138305)
                  ·
                    refine ⟨1579467862511850770353729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105957150015801027138305 1579467862511850770353729)
                    ·
                      refine ⟨1184600896883888077765297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579467862511850770353729 1184600896883888077765297)
                      ·
                        rfl

theorem cell23_2307002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_2307002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307002 prefixEnd_2307002 := by exact prefixLift 2307002
  have htrace : WordTrace (prefixWord ++ tailWord_2307002) baseStart_2307002 baseEnd_2307002 := by
    simpa [prefixWord, tailWord_2307002, baseEnd_2307002] using wordTrace_append hprefix tailTrace_2307002
  have hstable : (prefixWord ++ tailWord_2307002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307002).length < 2 ^ (prefixWord ++ tailWord_2307002).sum := by decide
  have hdescent : baseEnd_2307002 < baseStart_2307002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307014 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_2307014 : Nat := 118140960795 + 2307014 * 2 ^ 59
def prefixEnd_2307014 : Nat := 4983230072969 + 3 ^ 40 * 2307014 * 2
def baseEnd_2307014 : Nat := 1184607058651742030815243

theorem tailTrace_2307014 : CollatzResearch.WordTrace tailWord_2307014 prefixEnd_2307014 1184607058651742030815243 := by
  unfold tailWord_2307014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629491039502804983370003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56095808842726506311893397 2629491039502804983370003)
  ·
    refine ⟨3944236559254207475055005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629491039502804983370003 3944236559254207475055005)
    ·
      refine ⟨1479088709720327803145627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3944236559254207475055005 1479088709720327803145627)
      ·
        refine ⟨2218633064580491704718441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479088709720327803145627 2218633064580491704718441)
        ·
          refine ⟨1663974798435368778538831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2218633064580491704718441 1663974798435368778538831)
          ·
            refine ⟨2495962197653053167808247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663974798435368778538831 2495962197653053167808247)
            ·
              refine ⟨3743943296479579751712371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495962197653053167808247 3743943296479579751712371)
              ·
                refine ⟨5615914944719369627568557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3743943296479579751712371 5615914944719369627568557)
                ·
                  refine ⟨2105968104269763610338209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5615914944719369627568557 2105968104269763610338209)
                  ·
                    refine ⟨1579476078202322707753657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105968104269763610338209 1579476078202322707753657)
                    ·
                      refine ⟨1184607058651742030815243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579476078202322707753657 1184607058651742030815243)
                      ·
                        rfl

theorem cell23_2307014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_2307014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307014 prefixEnd_2307014 := by exact prefixLift 2307014
  have htrace : WordTrace (prefixWord ++ tailWord_2307014) baseStart_2307014 baseEnd_2307014 := by
    simpa [prefixWord, tailWord_2307014, baseEnd_2307014] using wordTrace_append hprefix tailTrace_2307014
  have hstable : (prefixWord ++ tailWord_2307014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307014).length < 2 ^ (prefixWord ++ tailWord_2307014).sum := by decide
  have hdescent : baseEnd_2307014 < baseStart_2307014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307018 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_2307018 : Nat := 118140960795 + 2307018 * 2 ^ 59
def prefixEnd_2307018 : Nat := 4983230072969 + 3 ^ 40 * 2307018 * 2
def baseEnd_2307018 : Nat := 1184609112574360015165223

theorem tailTrace_2307018 : CollatzResearch.WordTrace tailWord_2307018 prefixEnd_2307018 1184609112574360015165223 := by
  unfold tailWord_2307018
  simp only [CollatzResearch.WordTrace]
  refine ⟨21035964789018817037746427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56095906104050178767323805 21035964789018817037746427)
  ·
    refine ⟨31553947183528225556619641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21035964789018817037746427 31553947183528225556619641)
    ·
      refine ⟨23665460387646169167464731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31553947183528225556619641 23665460387646169167464731)
      ·
        refine ⟨35498190581469253751197097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23665460387646169167464731 35498190581469253751197097)
        ·
          refine ⟨26623642936101940313397823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35498190581469253751197097 26623642936101940313397823)
          ·
            refine ⟨39935464404152910470096735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26623642936101940313397823 39935464404152910470096735)
            ·
              refine ⟨59903196606229365705145103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39935464404152910470096735 59903196606229365705145103)
              ·
                refine ⟨89854794909344048557717655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59903196606229365705145103 89854794909344048557717655)
                ·
                  refine ⟨134782192364016072836576483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89854794909344048557717655 134782192364016072836576483)
                  ·
                    refine ⟨202173288546024109254864725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134782192364016072836576483 202173288546024109254864725)
                    ·
                      refine ⟨1184609112574360015165223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 202173288546024109254864725 1184609112574360015165223)
                      ·
                        rfl

theorem cell23_2307018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_2307018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307018 prefixEnd_2307018 := by exact prefixLift 2307018
  have htrace : WordTrace (prefixWord ++ tailWord_2307018) baseStart_2307018 baseEnd_2307018 := by
    simpa [prefixWord, tailWord_2307018, baseEnd_2307018] using wordTrace_append hprefix tailTrace_2307018
  have hstable : (prefixWord ++ tailWord_2307018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307018).length < 2 ^ (prefixWord ++ tailWord_2307018).sum := by decide
  have hdescent : baseEnd_2307018 < baseStart_2307018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307055 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 2, 5]
def baseStart_2307055 : Nat := 118140960795 + 2307055 * 2 ^ 59
def prefixEnd_2307055 : Nat := 4983230072969 + 3 ^ 40 * 2307055 * 2
def baseEnd_2307055 : Nat := 394876037119525456800851

theorem tailTrace_2307055 : CollatzResearch.WordTrace tailWord_2307055 prefixEnd_2307055 394876037119525456800851 := by
  unfold tailWord_2307055
  simp only [CollatzResearch.WordTrace]
  refine ⟨84145208656941223470082619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56096805771294148980055079 84145208656941223470082619)
  ·
    refine ⟨126217812985411835205123929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84145208656941223470082619 126217812985411835205123929)
    ·
      refine ⟨94663359739058876403842947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126217812985411835205123929 94663359739058876403842947)
      ·
        refine ⟨141995039608588314605764421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94663359739058876403842947 141995039608588314605764421)
        ·
          refine ⟨26624069926610308988580829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141995039608588314605764421 26624069926610308988580829)
          ·
            refine ⟨9984026222478865870717811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26624069926610308988580829 9984026222478865870717811)
            ·
              refine ⟨14976039333718298806076717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9984026222478865870717811 14976039333718298806076717)
              ·
                refine ⟨5616014750144362052278769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14976039333718298806076717 5616014750144362052278769)
                ·
                  refine ⟨4212011062608271539209077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5616014750144362052278769 4212011062608271539209077)
                  ·
                    refine ⟨394876037119525456800851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4212011062608271539209077 394876037119525456800851)
                    ·
                      rfl

theorem cell23_2307055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_2307055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307055 prefixEnd_2307055 := by exact prefixLift 2307055
  have htrace : WordTrace (prefixWord ++ tailWord_2307055) baseStart_2307055 baseEnd_2307055 := by
    simpa [prefixWord, tailWord_2307055, baseEnd_2307055] using wordTrace_append hprefix tailTrace_2307055
  have hstable : (prefixWord ++ tailWord_2307055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307055).length < 2 ^ (prefixWord ++ tailWord_2307055).sum := by decide
  have hdescent : baseEnd_2307055 < baseStart_2307055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307132 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 6]
def baseStart_2307132 : Nat := 118140960795 + 2307132 * 2 ^ 59
def prefixEnd_2307132 : Nat := 4983230072969 + 3 ^ 40 * 2307132 * 2
def baseEnd_2307132 : Nat := 131629738818774729904411

theorem tailTrace_2307132 : CollatzResearch.WordTrace tailWord_2307132 prefixEnd_2307132 131629738818774729904411 := by
  unfold tailWord_2307132
  simp only [CollatzResearch.WordTrace]
  refine ⟨42074008538831132810317825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56098678051774843747090433 42074008538831132810317825)
  ·
    refine ⟨31555506404123349607738369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42074008538831132810317825 31555506404123349607738369)
    ·
      refine ⟨23666629803092512205803777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31555506404123349607738369 23666629803092512205803777)
      ·
        refine ⟨17749972352319384154352833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23666629803092512205803777 17749972352319384154352833)
        ·
          refine ⟨13312479264239538115764625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17749972352319384154352833 13312479264239538115764625)
          ·
            refine ⟨9984359448179653586823469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13312479264239538115764625 9984359448179653586823469)
            ·
              refine ⟨3744134793067370095058801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9984359448179653586823469 3744134793067370095058801)
              ·
                refine ⟨2808101094800527571294101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744134793067370095058801 2808101094800527571294101)
                ·
                  refine ⟨131629738818774729904411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2808101094800527571294101 131629738818774729904411)
                  ·
                    rfl

theorem cell23_2307132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_2307132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307132 prefixEnd_2307132 := by exact prefixLift 2307132
  have htrace : WordTrace (prefixWord ++ tailWord_2307132) baseStart_2307132 baseEnd_2307132 := by
    simpa [prefixWord, tailWord_2307132, baseEnd_2307132] using wordTrace_append hprefix tailTrace_2307132
  have hstable : (prefixWord ++ tailWord_2307132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307132).length < 2 ^ (prefixWord ++ tailWord_2307132).sum := by decide
  have hdescent : baseEnd_2307132 < baseStart_2307132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307145 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 3, 5]
def baseStart_2307145 : Nat := 118140960795 + 2307145 * 2 ^ 59
def prefixEnd_2307145 : Nat := 4983230072969 + 3 ^ 40 * 2307145 * 2
def baseEnd_2307145 : Nat := 394891441539160339425713

theorem tailTrace_2307145 : CollatzResearch.WordTrace tailWord_2307145 prefixEnd_2307145 394891441539160339425713 := by
  unfold tailWord_2307145
  simp only [CollatzResearch.WordTrace]
  refine ⟨84148491226615168840858889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56098994151076779227239259 84148491226615168840858889)
  ·
    refine ⟨63111368419961376630644167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84148491226615168840858889 63111368419961376630644167)
    ·
      refine ⟨94667052629942064945966251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63111368419961376630644167 94667052629942064945966251)
      ·
        refine ⟨142000578944913097418949377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94667052629942064945966251 142000578944913097418949377)
        ·
          refine ⟨106500434208684823064212033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142000578944913097418949377 106500434208684823064212033)
          ·
            refine ⟨79875325656513617298159025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106500434208684823064212033 79875325656513617298159025)
            ·
              refine ⟨59906494242385212973619269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79875325656513617298159025 59906494242385212973619269)
              ·
                refine ⟨11232467670447227432553613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59906494242385212973619269 11232467670447227432553613)
                ·
                  refine ⟨4212175376417710287207605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11232467670447227432553613 4212175376417710287207605)
                  ·
                    refine ⟨394891441539160339425713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4212175376417710287207605 394891441539160339425713)
                    ·
                      rfl

theorem cell23_2307145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_2307145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307145 prefixEnd_2307145 := by exact prefixLift 2307145
  have htrace : WordTrace (prefixWord ++ tailWord_2307145) baseStart_2307145 baseEnd_2307145 := by
    simpa [prefixWord, tailWord_2307145, baseEnd_2307145] using wordTrace_append hprefix tailTrace_2307145
  have hstable : (prefixWord ++ tailWord_2307145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307145).length < 2 ^ (prefixWord ++ tailWord_2307145).sum := by decide
  have hdescent : baseEnd_2307145 < baseStart_2307145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307192 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 4, 4]
def baseStart_2307192 : Nat := 118140960795 + 2307192 * 2 ^ 59
def prefixEnd_2307192 : Nat := 4983230072969 + 3 ^ 40 * 2307192 * 2
def baseEnd_2307192 : Nat := 394899486069414111463141

theorem tailTrace_2307192 : CollatzResearch.WordTrace tailWord_2307192 prefixEnd_2307192 394899486069414111463141 := by
  unfold tailWord_2307192
  simp only [CollatzResearch.WordTrace]
  refine ⟨42075102728722447933909915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56100136971629930578546553 42075102728722447933909915)
  ·
    refine ⟨63112654093083671900864873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42075102728722447933909915 63112654093083671900864873)
    ·
      refine ⟨47334490569812753925648655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63112654093083671900864873 47334490569812753925648655)
      ·
        refine ⟨71001735854719130888472983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47334490569812753925648655 71001735854719130888472983)
        ·
          refine ⟨106502603782078696332709475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71001735854719130888472983 106502603782078696332709475)
          ·
            refine ⟨159753905673118044499064213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106502603782078696332709475 159753905673118044499064213)
            ·
              refine ⟨7488464328427408335893635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 159753905673118044499064213 7488464328427408335893635)
              ·
                refine ⟨11232696492641112503840453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7488464328427408335893635 11232696492641112503840453)
                ·
                  refine ⟨2106130592370208594470085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11232696492641112503840453 2106130592370208594470085)
                  ·
                    refine ⟨394899486069414111463141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2106130592370208594470085 394899486069414111463141)
                    ·
                      rfl

theorem cell23_2307192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_2307192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307192 prefixEnd_2307192 := by exact prefixLift 2307192
  have htrace : WordTrace (prefixWord ++ tailWord_2307192) baseStart_2307192 baseEnd_2307192 := by
    simpa [prefixWord, tailWord_2307192, baseEnd_2307192] using wordTrace_append hprefix tailTrace_2307192
  have hstable : (prefixWord ++ tailWord_2307192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307192).length < 2 ^ (prefixWord ++ tailWord_2307192).sum := by decide
  have hdescent : baseEnd_2307192 < baseStart_2307192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307193 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 3, 1, 3]
def baseStart_2307193 : Nat := 118140960795 + 2307193 * 2 ^ 59
def prefixEnd_2307193 : Nat := 4983230072969 + 3 ^ 40 * 2307193 * 2
def baseEnd_2307193 : Nat := 1184698971688896830476919

theorem tailTrace_2307193 : CollatzResearch.WordTrace tailWord_2307193 prefixEnd_2307193 1184698971688896830476919 := by
  unfold tailWord_2307193
  simp only [CollatzResearch.WordTrace]
  refine ⟨84150241930441273038606233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56100161286960848692404155 84150241930441273038606233)
  ·
    refine ⟨63112681447830954778954675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84150241930441273038606233 63112681447830954778954675)
    ·
      refine ⟨94669022171746432168432013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63112681447830954778954675 94669022171746432168432013)
      ·
        refine ⟨35500883314404912063162005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94669022171746432168432013 35500883314404912063162005)
        ·
          refine ⟨1664103905362730252960719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35500883314404912063162005 1664103905362730252960719)
          ·
            refine ⟨2496155858044095379441079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664103905362730252960719 2496155858044095379441079)
            ·
              refine ⟨3744233787066143069161619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496155858044095379441079 3744233787066143069161619)
              ·
                refine ⟨5616350680599214603742429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3744233787066143069161619 5616350680599214603742429)
                ·
                  refine ⟨2106131505224705476403411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5616350680599214603742429 2106131505224705476403411)
                  ·
                    refine ⟨3159197257837058214605117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2106131505224705476403411 3159197257837058214605117)
                    ·
                      refine ⟨1184698971688896830476919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3159197257837058214605117 1184698971688896830476919)
                      ·
                        rfl

theorem cell23_2307193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_2307193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307193 prefixEnd_2307193 := by exact prefixLift 2307193
  have htrace : WordTrace (prefixWord ++ tailWord_2307193) baseStart_2307193 baseEnd_2307193 := by
    simpa [prefixWord, tailWord_2307193, baseEnd_2307193] using wordTrace_append hprefix tailTrace_2307193
  have hstable : (prefixWord ++ tailWord_2307193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307193).length < 2 ^ (prefixWord ++ tailWord_2307193).sum := by decide
  have hdescent : baseEnd_2307193 < baseStart_2307193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307209 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 2, 4]
def baseStart_2307209 : Nat := 118140960795 + 2307209 * 2 ^ 59
def prefixEnd_2307209 : Nat := 4983230072969 + 3 ^ 40 * 2307209 * 2
def baseEnd_2307209 : Nat := 394902395793122922625615

theorem tailTrace_2307209 : CollatzResearch.WordTrace tailWord_2307209 prefixEnd_2307209 394902395793122922625615 := by
  unfold tailWord_2307209
  simp only [CollatzResearch.WordTrace]
  refine ⟨84150825498383307771188681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56100550332255538514125787 84150825498383307771188681)
  ·
    refine ⟨63113119123787480828391511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84150825498383307771188681 63113119123787480828391511)
    ·
      refine ⟨94669678685681221242587267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63113119123787480828391511 94669678685681221242587267)
      ·
        refine ⟨142004518028521831863880901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94669678685681221242587267 142004518028521831863880901)
        ·
          refine ⟨26625847130347843474477669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142004518028521831863880901 26625847130347843474477669)
          ·
            refine ⟨4992346336940220651464563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26625847130347843474477669 4992346336940220651464563)
            ·
              refine ⟨7488519505410330977196845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4992346336940220651464563 7488519505410330977196845)
              ·
                refine ⟨2808194814528874116448817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7488519505410330977196845 2808194814528874116448817)
                ·
                  refine ⟨2106146110896655587336613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2808194814528874116448817 2106146110896655587336613)
                  ·
                    refine ⟨394902395793122922625615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2106146110896655587336613 394902395793122922625615)
                    ·
                      rfl

theorem cell23_2307209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 4].length) (baseStart_2307209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307209 prefixEnd_2307209 := by exact prefixLift 2307209
  have htrace : WordTrace (prefixWord ++ tailWord_2307209) baseStart_2307209 baseEnd_2307209 := by
    simpa [prefixWord, tailWord_2307209, baseEnd_2307209] using wordTrace_append hprefix tailTrace_2307209
  have hstable : (prefixWord ++ tailWord_2307209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307209).length < 2 ^ (prefixWord ++ tailWord_2307209).sum := by decide
  have hdescent : baseEnd_2307209 < baseStart_2307209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307219 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 3]
def baseStart_2307219 : Nat := 118140960795 + 2307219 * 2 ^ 59
def prefixEnd_2307219 : Nat := 4983230072969 + 3 ^ 40 * 2307219 * 2
def baseEnd_2307219 : Nat := 1184712322185913728751799

theorem tailTrace_2307219 : CollatzResearch.WordTrace tailWord_2307219 prefixEnd_2307219 1184712322185913728751799 := by
  unfold tailWord_2307219
  simp only [CollatzResearch.WordTrace]
  refine ⟨84151190228347079479052711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56100793485564719652701807 84151190228347079479052711)
  ·
    refine ⟨126226785342520619218579067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84151190228347079479052711 126226785342520619218579067)
    ·
      refine ⟨189340178013780928827868601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126226785342520619218579067 189340178013780928827868601)
      ·
        refine ⟨142005133510335696620901451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189340178013780928827868601 142005133510335696620901451)
        ·
          refine ⟨213007700265503544931352177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142005133510335696620901451 213007700265503544931352177)
          ·
            refine ⟨159755775199127658698514133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213007700265503544931352177 159755775199127658698514133)
            ·
              refine ⟨3744275981229554500746425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 159755775199127658698514133 3744275981229554500746425)
              ·
                refine ⟨2808206985922165875559819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744275981229554500746425 2808206985922165875559819)
                ·
                  refine ⟨4212310478883248813339729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808206985922165875559819 4212310478883248813339729)
                  ·
                    refine ⟨3159232859162436610004797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4212310478883248813339729 3159232859162436610004797)
                    ·
                      refine ⟨1184712322185913728751799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3159232859162436610004797 1184712322185913728751799)
                      ·
                        rfl

theorem cell23_2307219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 3].length) (baseStart_2307219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307219 prefixEnd_2307219 := by exact prefixLift 2307219
  have htrace : WordTrace (prefixWord ++ tailWord_2307219) baseStart_2307219 baseEnd_2307219 := by
    simpa [prefixWord, tailWord_2307219, baseEnd_2307219] using wordTrace_append hprefix tailTrace_2307219
  have hstable : (prefixWord ++ tailWord_2307219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307219).length < 2 ^ (prefixWord ++ tailWord_2307219).sum := by decide
  have hdescent : baseEnd_2307219 < baseStart_2307219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307233 : List Nat := [1, 2, 3, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_2307233 : Nat := 118140960795 + 2307233 * 2 ^ 59
def prefixEnd_2307233 : Nat := 4983230072969 + 3 ^ 40 * 2307233 * 2
def baseEnd_2307233 : Nat := 1184719510915076673976735

theorem tailTrace_2307233 : CollatzResearch.WordTrace tailWord_2307233 prefixEnd_2307233 1184719510915076673976735 := by
  unfold tailWord_2307233
  simp only [CollatzResearch.WordTrace]
  refine ⟨84151700850296359870062353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56101133900197573246708235 84151700850296359870062353)
  ·
    refine ⟨63113775637722269902546765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84151700850296359870062353 63113775637722269902546765)
    ·
      refine ⟨23667665864145851213455037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63113775637722269902546765 23667665864145851213455037)
      ·
        refine ⟨8875374699054694205045639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23667665864145851213455037 8875374699054694205045639)
        ·
          refine ⟨13313062048582041307568459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8875374699054694205045639 13313062048582041307568459)
          ·
            refine ⟨19969593072873061961352689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13313062048582041307568459 19969593072873061961352689)
            ·
              refine ⟨14977194804654796471014517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19969593072873061961352689 14977194804654796471014517)
              ·
                refine ⟨1404112012936387169157611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14977194804654796471014517 1404112012936387169157611)
                ·
                  refine ⟨2106168019404580753736417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404112012936387169157611 2106168019404580753736417)
                  ·
                    refine ⟨1579626014553435565302313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2106168019404580753736417 1579626014553435565302313)
                    ·
                      refine ⟨1184719510915076673976735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579626014553435565302313 1184719510915076673976735)
                      ·
                        rfl

theorem cell23_2307233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_2307233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307233 prefixEnd_2307233 := by exact prefixLift 2307233
  have htrace : WordTrace (prefixWord ++ tailWord_2307233) baseStart_2307233 baseEnd_2307233 := by
    simpa [prefixWord, tailWord_2307233, baseEnd_2307233] using wordTrace_append hprefix tailTrace_2307233
  have hstable : (prefixWord ++ tailWord_2307233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307233).length < 2 ^ (prefixWord ++ tailWord_2307233).sum := by decide
  have hdescent : baseEnd_2307233 < baseStart_2307233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307235 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 4, 7]
def baseStart_2307235 : Nat := 118140960795 + 2307235 * 2 ^ 59
def prefixEnd_2307235 : Nat := 4983230072969 + 3 ^ 40 * 2307235 * 2
def baseEnd_2307235 : Nat := 394906845958795222050575

theorem tailTrace_2307235 : CollatzResearch.WordTrace tailWord_2307235 prefixEnd_2307235 394906845958795222050575 := by
  unfold tailWord_2307235
  simp only [CollatzResearch.WordTrace]
  refine ⟨84151773796289114211635159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56101182530859409474423439 84151773796289114211635159)
  ·
    refine ⟨126227660694433671317452739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84151773796289114211635159 126227660694433671317452739)
    ·
      refine ⟨189341491041650506976179109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126227660694433671317452739 189341491041650506976179109)
      ·
        refine ⟨35501529570309470058033583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189341491041650506976179109 35501529570309470058033583)
        ·
          refine ⟨53252294355464205087050375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35501529570309470058033583 53252294355464205087050375)
          ·
            refine ⟨79878441533196307630575563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53252294355464205087050375 79878441533196307630575563)
            ·
              refine ⟨119817662299794461445863345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79878441533196307630575563 119817662299794461445863345)
              ·
                refine ⟨89863246724845846084397509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119817662299794461445863345 89863246724845846084397509)
                ·
                  refine ⟨16849358760908596140824533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89863246724845846084397509 16849358760908596140824533)
                  ·
                    refine ⟨394906845958795222050575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16849358760908596140824533 394906845958795222050575)
                    ·
                      rfl

theorem cell23_2307235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 7].length) (baseStart_2307235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307235 prefixEnd_2307235 := by exact prefixLift 2307235
  have htrace : WordTrace (prefixWord ++ tailWord_2307235) baseStart_2307235 baseEnd_2307235 := by
    simpa [prefixWord, tailWord_2307235, baseEnd_2307235] using wordTrace_append hprefix tailTrace_2307235
  have hstable : (prefixWord ++ tailWord_2307235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307235).length < 2 ^ (prefixWord ++ tailWord_2307235).sum := by decide
  have hdescent : baseEnd_2307235 < baseStart_2307235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307250 : List Nat := [3, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_2307250 : Nat := 118140960795 + 2307250 * 2 ^ 59
def prefixEnd_2307250 : Nat := 4983230072969 + 3 ^ 40 * 2307250 * 2
def baseEnd_2307250 : Nat := 1184728240086203107464157

theorem tailTrace_2307250 : CollatzResearch.WordTrace tailWord_2307250 prefixEnd_2307250 1184728240086203107464157 := by
  unfold tailWord_2307250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21038080222808692943357801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56101547260823181182287469 21038080222808692943357801)
  ·
    refine ⟨15778560167106519707518351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21038080222808692943357801 15778560167106519707518351)
    ·
      refine ⟨23667840250659779561277527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15778560167106519707518351 23667840250659779561277527)
      ·
        refine ⟨35501760375989669341916291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23667840250659779561277527 35501760375989669341916291)
        ·
          refine ⟨53252640563984504012874437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35501760375989669341916291 53252640563984504012874437)
          ·
            refine ⟨9984870105747094502413957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53252640563984504012874437 9984870105747094502413957)
            ·
              refine ⟨1872163144827580219202617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9984870105747094502413957 1872163144827580219202617)
              ·
                refine ⟨1404122358620685164401963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1872163144827580219202617 1404122358620685164401963)
                ·
                  refine ⟨2106183537931027746602945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404122358620685164401963 2106183537931027746602945)
                  ·
                    refine ⟨1579637653448270809952209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2106183537931027746602945 1579637653448270809952209)
                    ·
                      refine ⟨1184728240086203107464157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579637653448270809952209 1184728240086203107464157)
                      ·
                        rfl

theorem cell23_2307250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_2307250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307250 prefixEnd_2307250 := by exact prefixLift 2307250
  have htrace : WordTrace (prefixWord ++ tailWord_2307250) baseStart_2307250 baseEnd_2307250 := by
    simpa [prefixWord, tailWord_2307250, baseEnd_2307250] using wordTrace_append hprefix tailTrace_2307250
  have hstable : (prefixWord ++ tailWord_2307250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307250).length < 2 ^ (prefixWord ++ tailWord_2307250).sum := by decide
  have hdescent : baseEnd_2307250 < baseStart_2307250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307282 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2307282 : Nat := 118140960795 + 2307282 * 2 ^ 59
def prefixEnd_2307282 : Nat := 4983230072969 + 3 ^ 40 * 2307282 * 2
def baseEnd_2307282 : Nat := 394914890489048994088003

theorem tailTrace_2307282 : CollatzResearch.WordTrace tailWord_2307282 prefixEnd_2307282 394914890489048994088003 := by
  unfold tailWord_2307282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21038372006779710309649025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56102325351412560825730733 21038372006779710309649025)
  ·
    refine ⟨15778779005084782732236769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21038372006779710309649025 15778779005084782732236769)
    ·
      refine ⟨11834084253813587049177577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15778779005084782732236769 11834084253813587049177577)
      ·
        refine ⟨8875563190360190286883183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11834084253813587049177577 8875563190360190286883183)
        ·
          refine ⟨13313344785540285430324775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8875563190360190286883183 13313344785540285430324775)
          ·
            refine ⟨19970017178310428145487163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13313344785540285430324775 19970017178310428145487163)
            ·
              refine ⟨29955025767465642218230745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19970017178310428145487163 29955025767465642218230745)
              ·
                refine ⟨22466269325599231663673059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29955025767465642218230745 22466269325599231663673059)
                ·
                  refine ⟨33699403988398847495509589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22466269325599231663673059 33699403988398847495509589)
                  ·
                    refine ⟨394914890489048994088003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33699403988398847495509589 394914890489048994088003)
                    ·
                      rfl

theorem cell23_2307282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2307282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307282 prefixEnd_2307282 := by exact prefixLift 2307282
  have htrace : WordTrace (prefixWord ++ tailWord_2307282) baseStart_2307282 baseEnd_2307282 := by
    simpa [prefixWord, tailWord_2307282, baseEnd_2307282] using wordTrace_append hprefix tailTrace_2307282
  have hstable : (prefixWord ++ tailWord_2307282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307282).length < 2 ^ (prefixWord ++ tailWord_2307282).sum := by decide
  have hdescent : baseEnd_2307282 < baseStart_2307282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307349 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_2307349 : Nat := 118140960795 + 2307349 * 2 ^ 59
def prefixEnd_2307349 : Nat := 4983230072969 + 3 ^ 40 * 2307349 * 2
def baseEnd_2307349 : Nat := 1184779074670998220126201

theorem tailTrace_2307349 : CollatzResearch.WordTrace tailWord_2307349 prefixEnd_2307349 1184779074670998220126201 := by
  unfold tailWord_2307349
  simp only [CollatzResearch.WordTrace]
  refine ⟨84155931717876111681285101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56103954478584074454190067 84155931717876111681285101)
  ·
    refine ⟨31558474394203541880481913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84155931717876111681285101 31558474394203541880481913)
    ·
      refine ⟨23668855795652656410361435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31558474394203541880481913 23668855795652656410361435)
      ·
        refine ⟨35503283693478984615542153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23668855795652656410361435 35503283693478984615542153)
        ·
          refine ⟨26627462770109238461656615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35503283693478984615542153 26627462770109238461656615)
          ·
            refine ⟨39941194155163857692484923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26627462770109238461656615 39941194155163857692484923)
            ·
              refine ⟨59911791232745786538727385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39941194155163857692484923 59911791232745786538727385)
              ·
                refine ⟨44933843424559339904045539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59911791232745786538727385 44933843424559339904045539)
                ·
                  refine ⟨67400765136839009856068309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44933843424559339904045539 67400765136839009856068309)
                  ·
                    refine ⟨1579705432894664293501601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 67400765136839009856068309 1579705432894664293501601)
                    ·
                      refine ⟨1184779074670998220126201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579705432894664293501601 1184779074670998220126201)
                      ·
                        rfl

theorem cell23_2307349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_2307349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307349 prefixEnd_2307349 := by exact prefixLift 2307349
  have htrace : WordTrace (prefixWord ++ tailWord_2307349) baseStart_2307349 baseEnd_2307349 := by
    simpa [prefixWord, tailWord_2307349, baseEnd_2307349] using wordTrace_append hprefix tailTrace_2307349
  have hstable : (prefixWord ++ tailWord_2307349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307349).length < 2 ^ (prefixWord ++ tailWord_2307349).sum := by decide
  have hdescent : baseEnd_2307349 < baseStart_2307349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307402 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 10]
def baseStart_2307402 : Nat := 118140960795 + 2307402 * 2 ^ 59
def prefixEnd_2307402 : Nat := 4983230072969 + 3 ^ 40 * 2307402 * 2
def baseEnd_2307402 : Nat := 131645143238409612529273

theorem tailTrace_2307402 : CollatzResearch.WordTrace tailWord_2307402 prefixEnd_2307402 131645143238409612529273 := by
  unfold tailWord_2307402
  simp only [CollatzResearch.WordTrace]
  refine ⟨21039466196671025433241115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56105243191122734488642973 21039466196671025433241115)
  ·
    refine ⟨31559199295006538149861673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21039466196671025433241115 31559199295006538149861673)
    ·
      refine ⟨23669399471254903612396255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31559199295006538149861673 23669399471254903612396255)
      ·
        refine ⟨35504099206882355418594383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23669399471254903612396255 35504099206882355418594383)
        ·
          refine ⟨53256148810323533127891575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35504099206882355418594383 53256148810323533127891575)
          ·
            refine ⟨79884223215485299691837363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53256148810323533127891575 79884223215485299691837363)
            ·
              refine ⟨119826334823227949537756045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79884223215485299691837363 119826334823227949537756045)
              ·
                refine ⟨44934875558710481076658517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119826334823227949537756045 44934875558710481076658517)
                ·
                  refine ⟨131645143238409612529273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 44934875558710481076658517 131645143238409612529273)
                  ·
                    rfl

theorem cell23_2307402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_2307402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307402 prefixEnd_2307402 := by exact prefixLift 2307402
  have htrace : WordTrace (prefixWord ++ tailWord_2307402) baseStart_2307402 baseEnd_2307402 := by
    simpa [prefixWord, tailWord_2307402, baseEnd_2307402] using wordTrace_append hprefix tailTrace_2307402
  have hstable : (prefixWord ++ tailWord_2307402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307402).length < 2 ^ (prefixWord ++ tailWord_2307402).sum := by decide
  have hdescent : baseEnd_2307402 < baseStart_2307402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307449 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 3, 5]
def baseStart_2307449 : Nat := 118140960795 + 2307449 * 2 ^ 59
def prefixEnd_2307449 : Nat := 4983230072969 + 3 ^ 40 * 2307449 * 2
def baseEnd_2307449 : Nat := 394943474245482609625247

theorem tailTrace_2307449 : CollatzResearch.WordTrace tailWord_2307449 prefixEnd_2307449 394943474245482609625247 := by
  unfold tailWord_2307449
  simp only [CollatzResearch.WordTrace]
  refine ⟨84159579017513828759925401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56106386011675885839950267 84159579017513828759925401)
  ·
    refine ⟨63119684263135371569944051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84159579017513828759925401 63119684263135371569944051)
    ·
      refine ⟨94679526394703057354916077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63119684263135371569944051 94679526394703057354916077)
      ·
        refine ⟨35504822398013646508093529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94679526394703057354916077 35504822398013646508093529)
        ·
          refine ⟨26628616798510234881070147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35504822398013646508093529 26628616798510234881070147)
          ·
            refine ⟨39942925197765352321605221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26628616798510234881070147 39942925197765352321605221)
            ·
              refine ⟨7489298474581003560300979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39942925197765352321605221 7489298474581003560300979)
              ·
                refine ⟨11233947711871505340451469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7489298474581003560300979 11233947711871505340451469)
                ·
                  refine ⟨4212730391951814502669301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11233947711871505340451469 4212730391951814502669301)
                  ·
                    refine ⟨394943474245482609625247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4212730391951814502669301 394943474245482609625247)
                    ·
                      rfl

theorem cell23_2307449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_2307449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307449 prefixEnd_2307449 := by exact prefixLift 2307449
  have htrace : WordTrace (prefixWord ++ tailWord_2307449) baseStart_2307449 baseEnd_2307449 := by
    simpa [prefixWord, tailWord_2307449, baseEnd_2307449] using wordTrace_append hprefix tailTrace_2307449
  have hstable : (prefixWord ++ tailWord_2307449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307449).length < 2 ^ (prefixWord ++ tailWord_2307449).sum := by decide
  have hdescent : baseEnd_2307449 < baseStart_2307449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307470 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_2307470 : Nat := 118140960795 + 2307470 * 2 ^ 59
def prefixEnd_2307470 : Nat := 4983230072969 + 3 ^ 40 * 2307470 * 2
def baseEnd_2307470 : Nat := 131649022870021360745905

theorem tailTrace_2307470 : CollatzResearch.WordTrace tailWord_2307470 prefixEnd_2307470 131649022870021360745905 := by
  unfold tailWord_2307470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10520043118804718668304983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56106896633625166230959909 10520043118804718668304983)
  ·
    refine ⟨15780064678207078002457475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10520043118804718668304983 15780064678207078002457475)
    ·
      refine ⟨23670097017310617003686213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15780064678207078002457475 23670097017310617003686213)
      ·
        refine ⟨4438143190745740688191165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23670097017310617003686213 4438143190745740688191165)
        ·
          refine ⟨1664303696529652758071687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4438143190745740688191165 1664303696529652758071687)
          ·
            refine ⟨2496455544794479137107531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664303696529652758071687 2496455544794479137107531)
            ·
              refine ⟨3744683317191718705661297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496455544794479137107531 3744683317191718705661297)
              ·
                refine ⟨2808512487893789029245973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744683317191718705661297 2808512487893789029245973)
                ·
                  refine ⟨131649022870021360745905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2808512487893789029245973 131649022870021360745905)
                  ·
                    rfl

theorem cell23_2307470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_2307470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307470 prefixEnd_2307470 := by exact prefixLift 2307470
  have htrace : WordTrace (prefixWord ++ tailWord_2307470) baseStart_2307470 baseEnd_2307470 := by
    simpa [prefixWord, tailWord_2307470, baseEnd_2307470] using wordTrace_append hprefix tailTrace_2307470
  have hstable : (prefixWord ++ tailWord_2307470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307470).length < 2 ^ (prefixWord ++ tailWord_2307470).sum := by decide
  have hdescent : baseEnd_2307470 < baseStart_2307470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307480 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2307480 : Nat := 118140960795 + 2307480 * 2 ^ 59
def prefixEnd_2307480 : Nat := 4983230072969 + 3 ^ 40 * 2307480 * 2
def baseEnd_2307480 : Nat := 1184846340636737207588099

theorem tailTrace_2307480 : CollatzResearch.WordTrace tailWord_2307480 prefixEnd_2307480 1184846340636737207588099 := by
  unfold tailWord_2307480
  simp only [CollatzResearch.WordTrace]
  refine ⟨42080354840200760527151947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56107139786934347369535929 42080354840200760527151947)
  ·
    refine ⟨63120532260301140790727921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42080354840200760527151947 63120532260301140790727921)
    ·
      refine ⟨47340399195225855593045941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63120532260301140790727921 47340399195225855593045941)
      ·
        refine ⟨4438162424552423961848057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47340399195225855593045941 4438162424552423961848057)
        ·
          refine ⟨3328621818414317971386043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4438162424552423961848057 3328621818414317971386043)
          ·
            refine ⟨4992932727621476957079065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328621818414317971386043 4992932727621476957079065)
            ·
              refine ⟨3744699545716107717809299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4992932727621476957079065 3744699545716107717809299)
              ·
                refine ⟨5617049318574161576713949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3744699545716107717809299 5617049318574161576713949)
                ·
                  refine ⟨2106393494465310591267731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5617049318574161576713949 2106393494465310591267731)
                  ·
                    refine ⟨3159590241697965886901597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2106393494465310591267731 3159590241697965886901597)
                    ·
                      refine ⟨1184846340636737207588099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3159590241697965886901597 1184846340636737207588099)
                      ·
                        rfl

theorem cell23_2307480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2307480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307480 prefixEnd_2307480 := by exact prefixLift 2307480
  have htrace : WordTrace (prefixWord ++ tailWord_2307480) baseStart_2307480 baseEnd_2307480 := by
    simpa [prefixWord, tailWord_2307480, baseEnd_2307480] using wordTrace_append hprefix tailTrace_2307480
  have hstable : (prefixWord ++ tailWord_2307480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307480).length < 2 ^ (prefixWord ++ tailWord_2307480).sum := by decide
  have hdescent : baseEnd_2307480 < baseStart_2307480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307563 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 1, 3, 2]
def baseStart_2307563 : Nat := 118140960795 + 2307563 * 2 ^ 59
def prefixEnd_2307563 : Nat := 4983230072969 + 3 ^ 40 * 2307563 * 2
def baseEnd_2307563 : Nat := 1184888959531060382850217

theorem tailTrace_2307563 : CollatzResearch.WordTrace tailWord_2307563 prefixEnd_2307563 1184888959531060382850217 := by
  unfold tailWord_2307563
  simp only [CollatzResearch.WordTrace]
  refine ⟨84163736939100826229575343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56109157959400550819716895 84163736939100826229575343)
  ·
    refine ⟨126245605408651239344363015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84163736939100826229575343 126245605408651239344363015)
    ·
      refine ⟨189368408112976859016544523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126245605408651239344363015 189368408112976859016544523)
      ·
        refine ⟨284052612169465288524816785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189368408112976859016544523 284052612169465288524816785)
        ·
          refine ⟨213039459127098966393612589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284052612169465288524816785 213039459127098966393612589)
          ·
            refine ⟨79889797172662112397604721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213039459127098966393612589 79889797172662112397604721)
            ·
              refine ⟨59917347879496584298203541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79889797172662112397604721 59917347879496584298203541)
              ·
                refine ⟨2808625681851402388978291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59917347879496584298203541 2808625681851402388978291)
                ·
                  refine ⟨4212938522777103583467437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808625681851402388978291 4212938522777103583467437)
                  ·
                    refine ⟨1579851946041413843800289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4212938522777103583467437 1579851946041413843800289)
                    ·
                      refine ⟨1184888959531060382850217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579851946041413843800289 1184888959531060382850217)
                      ·
                        rfl

theorem cell23_2307563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 3, 2].length) (baseStart_2307563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307563 prefixEnd_2307563 := by exact prefixLift 2307563
  have htrace : WordTrace (prefixWord ++ tailWord_2307563) baseStart_2307563 baseEnd_2307563 := by
    simpa [prefixWord, tailWord_2307563, baseEnd_2307563] using wordTrace_append hprefix tailTrace_2307563
  have hstable : (prefixWord ++ tailWord_2307563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307563).length < 2 ^ (prefixWord ++ tailWord_2307563).sum := by decide
  have hdescent : baseEnd_2307563 < baseStart_2307563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307588 : List Nat := [2, 3, 2, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_2307588 : Nat := 118140960795 + 2307588 * 2 ^ 59
def prefixEnd_2307588 : Nat := 4983230072969 + 3 ^ 40 * 2307588 * 2
def baseEnd_2307588 : Nat := 1184901796547422785037603

theorem tailTrace_2307588 : CollatzResearch.WordTrace tailWord_2307588 prefixEnd_2307588 1184901796547422785037603 := by
  unfold tailWord_2307588
  simp only [CollatzResearch.WordTrace]
  refine ⟨42082324382005127749617709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56109765842673503666156945 42082324382005127749617709)
  ·
    refine ⟨15780871643251922906106641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42082324382005127749617709 15780871643251922906106641)
    ·
      refine ⟨11835653732438942179579981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15780871643251922906106641 11835653732438942179579981)
      ·
        refine ⟨4438370149664603317342493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11835653732438942179579981 4438370149664603317342493)
        ·
          refine ⟨1664388806124226244003435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4438370149664603317342493 1664388806124226244003435)
          ·
            refine ⟨2496583209186339366005153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664388806124226244003435 2496583209186339366005153)
            ·
              refine ⟨1872437406889754524503865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496583209186339366005153 1872437406889754524503865)
              ·
                refine ⟨1404328055167315893377899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1872437406889754524503865 1404328055167315893377899)
                ·
                  refine ⟨2106492082750973840066849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404328055167315893377899 2106492082750973840066849)
                  ·
                    refine ⟨1579869062063230380050137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2106492082750973840066849 1579869062063230380050137)
                    ·
                      refine ⟨1184901796547422785037603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579869062063230380050137 1184901796547422785037603)
                      ·
                        rfl

theorem cell23_2307588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_2307588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307588 prefixEnd_2307588 := by exact prefixLift 2307588
  have htrace : WordTrace (prefixWord ++ tailWord_2307588) baseStart_2307588 baseEnd_2307588 := by
    simpa [prefixWord, tailWord_2307588, baseEnd_2307588] using wordTrace_append hprefix tailTrace_2307588
  have hstable : (prefixWord ++ tailWord_2307588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307588).length < 2 ^ (prefixWord ++ tailWord_2307588).sum := by decide
  have hdescent : baseEnd_2307588 < baseStart_2307588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307589 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_2307589 : Nat := 118140960795 + 2307589 * 2 ^ 59
def prefixEnd_2307589 : Nat := 4983230072969 + 3 ^ 40 * 2307589 * 2
def baseEnd_2307589 : Nat := 1184902310028077281125097

theorem tailTrace_2307589 : CollatzResearch.WordTrace tailWord_2307589 prefixEnd_2307589 1184902310028077281125097 := by
  unfold tailWord_2307589
  simp only [CollatzResearch.WordTrace]
  refine ⟨84164685237006632670021821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56109790158004421780014547 84164685237006632670021821)
  ·
    refine ⟨31561756963877487251258183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84164685237006632670021821 31561756963877487251258183)
    ·
      refine ⟨47342635445816230876887275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31561756963877487251258183 47342635445816230876887275)
      ·
        refine ⟨71013953168724346315330913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47342635445816230876887275 71013953168724346315330913)
        ·
          refine ⟨53260464876543259736498185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71013953168724346315330913 53260464876543259736498185)
          ·
            refine ⟨39945348657407444802373639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53260464876543259736498185 39945348657407444802373639)
            ·
              refine ⟨59918022986111167203560459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39945348657407444802373639 59918022986111167203560459)
              ·
                refine ⟨89877034479166750805340689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59918022986111167203560459 89877034479166750805340689)
                ·
                  refine ⟨67407775859375063104005517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89877034479166750805340689 67407775859375063104005517)
                  ·
                    refine ⟨25277915947265648664002069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67407775859375063104005517 25277915947265648664002069)
                    ·
                      refine ⟨1184902310028077281125097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25277915947265648664002069 1184902310028077281125097)
                      ·
                        rfl

theorem cell23_2307589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_2307589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307589 prefixEnd_2307589 := by exact prefixLift 2307589
  have htrace : WordTrace (prefixWord ++ tailWord_2307589) baseStart_2307589 baseEnd_2307589 := by
    simpa [prefixWord, tailWord_2307589, baseEnd_2307589] using wordTrace_append hprefix tailTrace_2307589
  have hstable : (prefixWord ++ tailWord_2307589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307589).length < 2 ^ (prefixWord ++ tailWord_2307589).sum := by decide
  have hdescent : baseEnd_2307589 < baseStart_2307589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307616 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 9]
def baseStart_2307616 : Nat := 118140960795 + 2307616 * 2 ^ 59
def prefixEnd_2307616 : Nat := 4983230072969 + 3 ^ 40 * 2307616 * 2
def baseEnd_2307616 : Nat := 131657352667305408387497

theorem tailTrace_2307616 : CollatzResearch.WordTrace tailWord_2307616 prefixEnd_2307616 131657352667305408387497 := by
  unfold tailWord_2307616
  simp only [CollatzResearch.WordTrace]
  refine ⟨42082835003954408140627351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56110446671939210854169801 42082835003954408140627351)
  ·
    refine ⟨63124252505931612210941027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42082835003954408140627351 63124252505931612210941027)
    ·
      refine ⟨94686378758897418316411541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63124252505931612210941027 94686378758897418316411541)
      ·
        refine ⟨4438424004323316483581791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94686378758897418316411541 4438424004323316483581791)
        ·
          refine ⟨6657636006484974725372687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4438424004323316483581791 6657636006484974725372687)
          ·
            refine ⟨9986454009727462088059031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6657636006484974725372687 9986454009727462088059031)
            ·
              refine ⟨14979681014591193132088547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9986454009727462088059031 14979681014591193132088547)
              ·
                refine ⟨22469521521886789698132821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14979681014591193132088547 22469521521886789698132821)
                ·
                  refine ⟨131657352667305408387497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22469521521886789698132821 131657352667305408387497)
                  ·
                    rfl

theorem cell23_2307616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 9].length) (baseStart_2307616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307616 prefixEnd_2307616 := by exact prefixLift 2307616
  have htrace : WordTrace (prefixWord ++ tailWord_2307616) baseStart_2307616 baseEnd_2307616 := by
    simpa [prefixWord, tailWord_2307616, baseEnd_2307616] using wordTrace_append hprefix tailTrace_2307616
  have hstable : (prefixWord ++ tailWord_2307616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307616).length < 2 ^ (prefixWord ++ tailWord_2307616).sum := by decide
  have hdescent : baseEnd_2307616 < baseStart_2307616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307644 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_2307644 : Nat := 118140960795 + 2307644 * 2 ^ 59
def prefixEnd_2307644 : Nat := 4983230072969 + 3 ^ 40 * 2307644 * 2
def baseEnd_2307644 : Nat := 1184930551464074565937345

theorem tailTrace_2307644 : CollatzResearch.WordTrace tailWord_2307644 prefixEnd_2307644 1184930551464074565937345 := by
  unfold tailWord_2307644
  simp only [CollatzResearch.WordTrace]
  refine ⟨42083345625903688531636993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56111127501204918042182657 42083345625903688531636993)
  ·
    refine ⟨31562509219427766398727745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42083345625903688531636993 31562509219427766398727745)
    ·
      refine ⟨23671881914570824799045809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31562509219427766398727745 23671881914570824799045809)
      ·
        refine ⟨17753911435928118599284357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23671881914570824799045809 17753911435928118599284357)
        ·
          refine ⟨3328858394236522237365817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17753911435928118599284357 3328858394236522237365817)
          ·
            refine ⟨2496643795677391678024363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3328858394236522237365817 2496643795677391678024363)
            ·
              refine ⟨3744965693516087517036545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496643795677391678024363 3744965693516087517036545)
              ·
                refine ⟨2808724270137065637777409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744965693516087517036545 2808724270137065637777409)
                ·
                  refine ⟨2106543202602799228333057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2808724270137065637777409 2106543202602799228333057)
                  ·
                    refine ⟨1579907401952099421249793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2106543202602799228333057 1579907401952099421249793)
                    ·
                      refine ⟨1184930551464074565937345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579907401952099421249793 1184930551464074565937345)
                      ·
                        rfl

theorem cell23_2307644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_2307644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307644 prefixEnd_2307644 := by exact prefixLift 2307644
  have htrace : WordTrace (prefixWord ++ tailWord_2307644) baseStart_2307644 baseEnd_2307644 := by
    simpa [prefixWord, tailWord_2307644, baseEnd_2307644] using wordTrace_append hprefix tailTrace_2307644
  have hstable : (prefixWord ++ tailWord_2307644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307644).length < 2 ^ (prefixWord ++ tailWord_2307644).sum := by decide
  have hdescent : baseEnd_2307644 < baseStart_2307644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307661 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_2307661 : Nat := 118140960795 + 2307661 * 2 ^ 59
def prefixEnd_2307661 : Nat := 4983230072969 + 3 ^ 40 * 2307661 * 2
def baseEnd_2307661 : Nat := 1184939280635200999424767

theorem tailTrace_2307661 : CollatzResearch.WordTrace tailWord_2307661 prefixEnd_2307661 1184939280635200999424767 := by
  unfold tailWord_2307661
  simp only [CollatzResearch.WordTrace]
  refine ⟨84167311292745788966642837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56111540861830525977761891 84167311292745788966642837)
  ·
    refine ⟨3945342716847458857811383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84167311292745788966642837 3945342716847458857811383)
    ·
      refine ⟨5918014075271188286717075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3945342716847458857811383 5918014075271188286717075)
      ·
        refine ⟨8877021112906782430075613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918014075271188286717075 8877021112906782430075613)
        ·
          refine ⟨3328882917340043411278355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8877021112906782430075613 3328882917340043411278355)
          ·
            refine ⟨4993324376010065116917533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328882917340043411278355 4993324376010065116917533)
            ·
              refine ⟨1872496641003774418844075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4993324376010065116917533 1872496641003774418844075)
              ·
                refine ⟨2808744961505661628266113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872496641003774418844075 2808744961505661628266113)
                ·
                  refine ⟨2106558721129246221199585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2808744961505661628266113 2106558721129246221199585)
                  ·
                    refine ⟨1579919040846934665899689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2106558721129246221199585 1579919040846934665899689)
                    ·
                      refine ⟨1184939280635200999424767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579919040846934665899689 1184939280635200999424767)
                      ·
                        rfl

theorem cell23_2307661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_2307661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307661 prefixEnd_2307661 := by exact prefixLift 2307661
  have htrace : WordTrace (prefixWord ++ tailWord_2307661) baseStart_2307661 baseEnd_2307661 := by
    simpa [prefixWord, tailWord_2307661, baseEnd_2307661] using wordTrace_append hprefix tailTrace_2307661
  have hstable : (prefixWord ++ tailWord_2307661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307661).length < 2 ^ (prefixWord ++ tailWord_2307661).sum := by decide
  have hdescent : baseEnd_2307661 < baseStart_2307661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307760 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 2, 3, 2]
def baseStart_2307760 : Nat := 118140960795 + 2307760 * 2 ^ 59
def prefixEnd_2307760 : Nat := 4983230072969 + 3 ^ 40 * 2307760 * 2
def baseEnd_2307760 : Nat := 1184990115219996112086811

theorem tailTrace_2307760 : CollatzResearch.WordTrace tailWord_2307760 prefixEnd_2307760 1184990115219996112086811 := by
  unfold tailWord_2307760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42085461059693564437248367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56113948079591419249664489 42085461059693564437248367)
  ·
    refine ⟨63128191589540346655872551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42085461059693564437248367 63128191589540346655872551)
    ·
      refine ⟨94692287384310519983808827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63128191589540346655872551 94692287384310519983808827)
      ·
        refine ⟨142038431076465779975713241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94692287384310519983808827 142038431076465779975713241)
        ·
          refine ⟨106528823307349334981784931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142038431076465779975713241 106528823307349334981784931)
          ·
            refine ⟨159793234961024002472677397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106528823307349334981784931 159793234961024002472677397)
            ·
              refine ⟨7490307888798000115906753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 159793234961024002472677397 7490307888798000115906753)
              ·
                refine ⟨5617730916598500086930065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7490307888798000115906753 5617730916598500086930065)
                ·
                  refine ⟨4213298187448875065197549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5617730916598500086930065 4213298187448875065197549)
                  ·
                    refine ⟨1579986820293328149449081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4213298187448875065197549 1579986820293328149449081)
                    ·
                      refine ⟨1184990115219996112086811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1579986820293328149449081 1184990115219996112086811)
                      ·
                        rfl

theorem cell23_2307760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 3, 2].length) (baseStart_2307760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307760 prefixEnd_2307760 := by exact prefixLift 2307760
  have htrace : WordTrace (prefixWord ++ tailWord_2307760) baseStart_2307760 baseEnd_2307760 := by
    simpa [prefixWord, tailWord_2307760, baseEnd_2307760] using wordTrace_append hprefix tailTrace_2307760
  have hstable : (prefixWord ++ tailWord_2307760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307760).length < 2 ^ (prefixWord ++ tailWord_2307760).sum := by decide
  have hdescent : baseEnd_2307760 < baseStart_2307760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307773 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_2307773 : Nat := 118140960795 + 2307773 * 2 ^ 59
def prefixEnd_2307773 : Nat := 4983230072969 + 3 ^ 40 * 2307773 * 2
def baseEnd_2307773 : Nat := 1184996790468504561224251

theorem tailTrace_2307773 : CollatzResearch.WordTrace tailWord_2307773 prefixEnd_2307773 1184996790468504561224251 := by
  unfold tailWord_2307773
  simp only [CollatzResearch.WordTrace]
  refine ⟨84171396268340032094719973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56114264178893354729813315 84171396268340032094719973)
  ·
    refine ⟨15782136800313756017759995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84171396268340032094719973 15782136800313756017759995)
    ·
      refine ⟨23673205200470634026639993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15782136800313756017759995 23673205200470634026639993)
      ·
        refine ⟨17754903900352975519979995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23673205200470634026639993 17754903900352975519979995)
        ·
          refine ⟨26632355850529463279969993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17754903900352975519979995 26632355850529463279969993)
          ·
            refine ⟨19974266887897097459977495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26632355850529463279969993 19974266887897097459977495)
            ·
              refine ⟨29961400331845646189966243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19974266887897097459977495 29961400331845646189966243)
              ·
                refine ⟨44942100497768469284949365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29961400331845646189966243 44942100497768469284949365)
                ·
                  refine ⟨4213321921665793995464003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44942100497768469284949365 4213321921665793995464003)
                  ·
                    refine ⟨6319982882498690993196005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4213321921665793995464003 6319982882498690993196005)
                    ·
                      refine ⟨1184996790468504561224251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6319982882498690993196005 1184996790468504561224251)
                      ·
                        rfl

theorem cell23_2307773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_2307773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307773 prefixEnd_2307773 := by exact prefixLift 2307773
  have htrace : WordTrace (prefixWord ++ tailWord_2307773) baseStart_2307773 baseEnd_2307773 := by
    simpa [prefixWord, tailWord_2307773, baseEnd_2307773] using wordTrace_append hprefix tailTrace_2307773
  have hstable : (prefixWord ++ tailWord_2307773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307773).length < 2 ^ (prefixWord ++ tailWord_2307773).sum := by decide
  have hdescent : baseEnd_2307773 < baseStart_2307773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307783 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 1, 6]
def baseStart_2307783 : Nat := 118140960795 + 2307783 * 2 ^ 59
def prefixEnd_2307783 : Nat := 4983230072969 + 3 ^ 40 * 2307783 * 2
def baseEnd_2307783 : Nat := 395000641758349840699735

theorem tailTrace_2307783 : CollatzResearch.WordTrace tailWord_2307783 prefixEnd_2307783 395000641758349840699735 := by
  unfold tailWord_2307783
  simp only [CollatzResearch.WordTrace]
  refine ⟨84171760998303803802584003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56114507332202535868389335 84171760998303803802584003)
  ·
    refine ⟨126257641497455705703876005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84171760998303803802584003 126257641497455705703876005)
    ·
      refine ⟨23673307780772944819476751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126257641497455705703876005 23673307780772944819476751)
      ·
        refine ⟨35509961671159417229215127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23673307780772944819476751 35509961671159417229215127)
        ·
          refine ⟨53264942506739125843822691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35509961671159417229215127 53264942506739125843822691)
          ·
            refine ⟨79897413760108688765734037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53264942506739125843822691 79897413760108688765734037)
            ·
              refine ⟨3745191270005094785893783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79897413760108688765734037 3745191270005094785893783)
              ·
                refine ⟨5617786905007642178840675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3745191270005094785893783 5617786905007642178840675)
                ·
                  refine ⟨8426680357511463268261013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5617786905007642178840675 8426680357511463268261013)
                  ·
                    refine ⟨395000641758349840699735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8426680357511463268261013 395000641758349840699735)
                    ·
                      rfl

theorem cell23_2307783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_2307783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307783 prefixEnd_2307783 := by exact prefixLift 2307783
  have htrace : WordTrace (prefixWord ++ tailWord_2307783) baseStart_2307783 baseEnd_2307783 := by
    simpa [prefixWord, tailWord_2307783, baseEnd_2307783] using wordTrace_append hprefix tailTrace_2307783
  have hstable : (prefixWord ++ tailWord_2307783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307783).length < 2 ^ (prefixWord ++ tailWord_2307783).sum := by decide
  have hdescent : baseEnd_2307783 < baseStart_2307783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307790 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_2307790 : Nat := 118140960795 + 2307790 * 2 ^ 59
def prefixEnd_2307790 : Nat := 4983230072969 + 3 ^ 40 * 2307790 * 2
def baseEnd_2307790 : Nat := 1185005519639630994711673

theorem tailTrace_2307790 : CollatzResearch.WordTrace tailWord_2307790 prefixEnd_2307790 1185005519639630994711673 := by
  unfold tailWord_2307790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10521502038659805499761103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56114677539518962665392549 10521502038659805499761103)
  ·
    refine ⟨15782253057989708249641655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10521502038659805499761103 15782253057989708249641655)
    ·
      refine ⟨23673379586984562374462483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15782253057989708249641655 23673379586984562374462483)
      ·
        refine ⟨35510069380476843561693725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23673379586984562374462483 35510069380476843561693725)
        ·
          refine ⟨13316276017678816335635147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35510069380476843561693725 13316276017678816335635147)
          ·
            refine ⟨19974414026518224503452721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13316276017678816335635147 19974414026518224503452721)
            ·
              refine ⟨14980810519888668377589541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19974414026518224503452721 14980810519888668377589541)
              ·
                refine ⟨2808901972479125320798039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14980810519888668377589541 2808901972479125320798039)
                ·
                  refine ⟨4213352958718687981197059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808901972479125320798039 4213352958718687981197059)
                  ·
                    refine ⟨6320029438078031971795589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4213352958718687981197059 6320029438078031971795589)
                    ·
                      refine ⟨1185005519639630994711673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6320029438078031971795589 1185005519639630994711673)
                      ·
                        rfl

theorem cell23_2307790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_2307790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307790 prefixEnd_2307790 := by exact prefixLift 2307790
  have htrace : WordTrace (prefixWord ++ tailWord_2307790) baseStart_2307790 baseEnd_2307790 := by
    simpa [prefixWord, tailWord_2307790, baseEnd_2307790] using wordTrace_append hprefix tailTrace_2307790
  have hstable : (prefixWord ++ tailWord_2307790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307790).length < 2 ^ (prefixWord ++ tailWord_2307790).sum := by decide
  have hdescent : baseEnd_2307790 < baseStart_2307790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307794 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_2307794 : Nat := 118140960795 + 2307794 * 2 ^ 59
def prefixEnd_2307794 : Nat := 4983230072969 + 3 ^ 40 * 2307794 * 2
def baseEnd_2307794 : Nat := 1185007573562248979061655

theorem tailTrace_2307794 : CollatzResearch.WordTrace tailWord_2307794 prefixEnd_2307794 1185007573562248979061655 := by
  unfold tailWord_2307794
  simp only [CollatzResearch.WordTrace]
  refine ⟨21043040550315988170308609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56114774800842635120822957 21043040550315988170308609)
  ·
    refine ⟨15782280412736991127731457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21043040550315988170308609 15782280412736991127731457)
    ·
      refine ⟨11836710309552743345798593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15782280412736991127731457 11836710309552743345798593)
      ·
        refine ⟨8877532732164557509348945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11836710309552743345798593 8877532732164557509348945)
        ·
          refine ⟨6658149549123418132011709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8877532732164557509348945 6658149549123418132011709)
          ·
            refine ⟨2496806080921281799504391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6658149549123418132011709 2496806080921281799504391)
            ·
              refine ⟨3745209121381922699256587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496806080921281799504391 3745209121381922699256587)
              ·
                refine ⟨5617813682072884048884881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3745209121381922699256587 5617813682072884048884881)
                ·
                  refine ⟨4213360261554663036663661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5617813682072884048884881 4213360261554663036663661)
                  ·
                    refine ⟨1580010098082998638748873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4213360261554663036663661 1580010098082998638748873)
                    ·
                      refine ⟨1185007573562248979061655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580010098082998638748873 1185007573562248979061655)
                      ·
                        rfl

theorem cell23_2307794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_2307794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307794 prefixEnd_2307794 := by exact prefixLift 2307794
  have htrace : WordTrace (prefixWord ++ tailWord_2307794) baseStart_2307794 baseEnd_2307794 := by
    simpa [prefixWord, tailWord_2307794, baseEnd_2307794] using wordTrace_append hprefix tailTrace_2307794
  have hstable : (prefixWord ++ tailWord_2307794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307794).length < 2 ^ (prefixWord ++ tailWord_2307794).sum := by decide
  have hdescent : baseEnd_2307794 < baseStart_2307794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307847 : List Nat := [1, 1, 4, 4, 2, 2, 2, 7]
def baseStart_2307847 : Nat := 118140960795 + 2307847 * 2 ^ 59
def prefixEnd_2307847 : Nat := 4983230072969 + 3 ^ 40 * 2307847 * 2
def baseEnd_2307847 : Nat := 43890177334701380433293

theorem tailTrace_2307847 : CollatzResearch.WordTrace tailWord_2307847 prefixEnd_2307847 43890177334701380433293 := by
  unfold tailWord_2307847
  simp only [CollatzResearch.WordTrace]
  refine ⟨84174095270071942732913795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56116063513381295155275863 84174095270071942732913795)
  ·
    refine ⟨126261142905107914099370693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84174095270071942732913795 126261142905107914099370693)
    ·
      refine ⟨23673964294707733893632005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126261142905107914099370693 23673964294707733893632005)
      ·
        refine ⟨4438868305257700105056001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23673964294707733893632005 4438868305257700105056001)
        ·
          refine ⟨3329151228943275078792001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4438868305257700105056001 3329151228943275078792001)
          ·
            refine ⟨2496863421707456309094001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3329151228943275078792001 2496863421707456309094001)
            ·
              refine ⟨1872647566280592231820501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496863421707456309094001 1872647566280592231820501)
              ·
                refine ⟨43890177334701380433293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1872647566280592231820501 43890177334701380433293)
                ·
                  rfl

theorem cell23_2307847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 7].length) (baseStart_2307847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307847 prefixEnd_2307847 := by exact prefixLift 2307847
  have htrace : WordTrace (prefixWord ++ tailWord_2307847) baseStart_2307847 baseEnd_2307847 := by
    simpa [prefixWord, tailWord_2307847, baseEnd_2307847] using wordTrace_append hprefix tailTrace_2307847
  have hstable : (prefixWord ++ tailWord_2307847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307847).length < 2 ^ (prefixWord ++ tailWord_2307847).sum := by decide
  have hdescent : baseEnd_2307847 < baseStart_2307847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307858 : List Nat := [3, 2, 4, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2307858 : Nat := 118140960795 + 2307858 * 2 ^ 59
def prefixEnd_2307858 : Nat := 4983230072969 + 3 ^ 40 * 2307858 * 2
def baseEnd_2307858 : Nat := 1185040436324136728661361

theorem tailTrace_2307858 : CollatzResearch.WordTrace tailWord_2307858 prefixEnd_2307858 1185040436324136728661361 := by
  unfold tailWord_2307858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21043624118258022902891057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56116330982021394407709485 21043624118258022902891057)
  ·
    refine ⟨15782718088693517177168293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21043624118258022902891057 15782718088693517177168293)
    ·
      refine ⟨2959259641630034470719055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15782718088693517177168293 2959259641630034470719055)
      ·
        refine ⟨4438889462445051706078583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959259641630034470719055 4438889462445051706078583)
        ·
          refine ⟨6658334193667577559117875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4438889462445051706078583 6658334193667577559117875)
          ·
            refine ⟨9987501290501366338676813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658334193667577559117875 9987501290501366338676813)
            ·
              refine ⟨3745312983938012377003805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9987501290501366338676813 3745312983938012377003805)
              ·
                refine ⟨1404492368976754641376427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3745312983938012377003805 1404492368976754641376427)
                ·
                  refine ⟨2106738553465131962064641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404492368976754641376427 2106738553465131962064641)
                  ·
                    refine ⟨1580053915098848971548481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2106738553465131962064641 1580053915098848971548481)
                    ·
                      refine ⟨1185040436324136728661361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580053915098848971548481 1185040436324136728661361)
                      ·
                        rfl

theorem cell23_2307858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2307858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307858 prefixEnd_2307858 := by exact prefixLift 2307858
  have htrace : WordTrace (prefixWord ++ tailWord_2307858) baseStart_2307858 baseEnd_2307858 := by
    simpa [prefixWord, tailWord_2307858, baseEnd_2307858] using wordTrace_append hprefix tailTrace_2307858
  have hstable : (prefixWord ++ tailWord_2307858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307858).length < 2 ^ (prefixWord ++ tailWord_2307858).sum := by decide
  have hdescent : baseEnd_2307858 < baseStart_2307858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307891 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 2, 1, 3]
def baseStart_2307891 : Nat := 118140960795 + 2307891 * 2 ^ 59
def prefixEnd_2307891 : Nat := 4983230072969 + 3 ^ 40 * 2307891 * 2
def baseEnd_2307891 : Nat := 1185057381185735099548709

theorem tailTrace_2307891 : CollatzResearch.WordTrace tailWord_2307891 prefixEnd_2307891 1185057381185735099548709 := by
  unfold tailWord_2307891
  simp only [CollatzResearch.WordTrace]
  refine ⟨84175700081912538247515527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56117133387941692165010351 84175700081912538247515527)
  ·
    refine ⟨126263550122868807371273291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84175700081912538247515527 126263550122868807371273291)
    ·
      refine ⟨189395325184303211056909937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126263550122868807371273291 189395325184303211056909937)
      ·
        refine ⟨142046493888227408292682453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189395325184303211056909937 142046493888227408292682453)
        ·
          refine ⟨3329214700505329881859745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 142046493888227408292682453 3329214700505329881859745)
          ·
            refine ⟨2496911025378997411394809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3329214700505329881859745 2496911025378997411394809)
            ·
              refine ⟨1872683269034248058546107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496911025378997411394809 1872683269034248058546107)
              ·
                refine ⟨2809024903551372087819161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872683269034248058546107 2809024903551372087819161)
                ·
                  refine ⟨2106768677663529065864371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2809024903551372087819161 2106768677663529065864371)
                  ·
                    refine ⟨3160153016495293598796557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2106768677663529065864371 3160153016495293598796557)
                    ·
                      refine ⟨1185057381185735099548709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3160153016495293598796557 1185057381185735099548709)
                      ·
                        rfl

theorem cell23_2307891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 1, 3].length) (baseStart_2307891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307891 prefixEnd_2307891 := by exact prefixLift 2307891
  have htrace : WordTrace (prefixWord ++ tailWord_2307891) baseStart_2307891 baseEnd_2307891 := by
    simpa [prefixWord, tailWord_2307891, baseEnd_2307891] using wordTrace_append hprefix tailTrace_2307891
  have hstable : (prefixWord ++ tailWord_2307891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307891).length < 2 ^ (prefixWord ++ tailWord_2307891).sum := by decide
  have hdescent : baseEnd_2307891 < baseStart_2307891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307901 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_2307901 : Nat := 118140960795 + 2307901 * 2 ^ 59
def prefixEnd_2307901 : Nat := 4983230072969 + 3 ^ 40 * 2307901 * 2
def baseEnd_2307901 : Nat := 1185062515992280060423663

theorem tailTrace_2307901 : CollatzResearch.WordTrace tailWord_2307901 prefixEnd_2307901 1185062515992280060423663 := by
  unfold tailWord_2307901
  simp only [CollatzResearch.WordTrace]
  refine ⟨84176064811876309955379557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56117376541250873303586371 84176064811876309955379557)
  ·
    refine ⟨15783012152226808116633667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84176064811876309955379557 15783012152226808116633667)
    ·
      refine ⟨23674518228340212174950501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15783012152226808116633667 23674518228340212174950501)
      ·
        refine ⟨4438972167813789782803219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23674518228340212174950501 4438972167813789782803219)
        ·
          refine ⟨6658458251720684674204829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4438972167813789782803219 6658458251720684674204829)
          ·
            refine ⟨2496921844395256752826811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6658458251720684674204829 2496921844395256752826811)
            ·
              refine ⟨3745382766592885129240217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496921844395256752826811 3745382766592885129240217)
              ·
                refine ⟨2809037074944663846930163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3745382766592885129240217 2809037074944663846930163)
                ·
                  refine ⟨4213555612416995770395245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809037074944663846930163 4213555612416995770395245)
                  ·
                    refine ⟨1580083354656373413898217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4213555612416995770395245 1580083354656373413898217)
                    ·
                      refine ⟨1185062515992280060423663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580083354656373413898217 1185062515992280060423663)
                      ·
                        rfl

theorem cell23_2307901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_2307901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307901 prefixEnd_2307901 := by exact prefixLift 2307901
  have htrace : WordTrace (prefixWord ++ tailWord_2307901) baseStart_2307901 baseEnd_2307901 := by
    simpa [prefixWord, tailWord_2307901, baseEnd_2307901] using wordTrace_append hprefix tailTrace_2307901
  have hstable : (prefixWord ++ tailWord_2307901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307901).length < 2 ^ (prefixWord ++ tailWord_2307901).sum := by decide
  have hdescent : baseEnd_2307901 < baseStart_2307901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307917 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2307917 : Nat := 118140960795 + 2307917 * 2 ^ 59
def prefixEnd_2307917 : Nat := 4983230072969 + 3 ^ 40 * 2307917 * 2
def baseEnd_2307917 : Nat := 1185070731682751997823589

theorem tailTrace_2307917 : CollatzResearch.WordTrace tailWord_2307917 prefixEnd_2307917 1185070731682751997823589 := by
  unfold tailWord_2307917
  simp only [CollatzResearch.WordTrace]
  refine ⟨84176648379818344687962005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56117765586545563125308003 84176648379818344687962005)
  ·
    refine ⟨3945780392803984907248219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84176648379818344687962005 3945780392803984907248219)
    ·
      refine ⟨5918670589205977360872329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3945780392803984907248219 5918670589205977360872329)
      ·
        refine ⟨4439002941904483020654247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5918670589205977360872329 4439002941904483020654247)
        ·
          refine ⟨6658504412856724530981371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439002941904483020654247 6658504412856724530981371)
          ·
            refine ⟨9987756619285086796472057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658504412856724530981371 9987756619285086796472057)
            ·
              refine ⟨7490817464463815097354043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9987756619285086796472057 7490817464463815097354043)
              ·
                refine ⟨11236226196695722646031065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7490817464463815097354043 11236226196695722646031065)
                ·
                  refine ⟨8427169647521791984523299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11236226196695722646031065 8427169647521791984523299)
                  ·
                    refine ⟨12640754471282687976784949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8427169647521791984523299 12640754471282687976784949)
                    ·
                      refine ⟨1185070731682751997823589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12640754471282687976784949 1185070731682751997823589)
                      ·
                        rfl

theorem cell23_2307917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2307917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307917 prefixEnd_2307917 := by exact prefixLift 2307917
  have htrace : WordTrace (prefixWord ++ tailWord_2307917) baseStart_2307917 baseEnd_2307917 := by
    simpa [prefixWord, tailWord_2307917, baseEnd_2307917] using wordTrace_append hprefix tailTrace_2307917
  have hstable : (prefixWord ++ tailWord_2307917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307917).length < 2 ^ (prefixWord ++ tailWord_2307917).sum := by decide
  have hdescent : baseEnd_2307917 < baseStart_2307917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307920 : List Nat := [2, 1, 1, 1, 1, 4, 1, 7, 5]
def baseStart_2307920 : Nat := 118140960795 + 2307920 * 2 ^ 59
def prefixEnd_2307920 : Nat := 4983230072969 + 3 ^ 40 * 2307920 * 2
def baseEnd_2307920 : Nat := 131674696902746165120675

theorem tailTrace_2307920 : CollatzResearch.WordTrace tailWord_2307920 prefixEnd_2307920 131674696902746165120675 := by
  unfold tailWord_2307920
  simp only [CollatzResearch.WordTrace]
  refine ⟨42088378899403738100160607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56117838532538317466880809 42088378899403738100160607)
  ·
    refine ⟨63132568349105607150240911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42088378899403738100160607 63132568349105607150240911)
    ·
      refine ⟨94698852523658410725361367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63132568349105607150240911 94698852523658410725361367)
      ·
        refine ⟨142048278785487616088042051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94698852523658410725361367 142048278785487616088042051)
        ·
          refine ⟨213072418178231424132063077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142048278785487616088042051 213072418178231424132063077)
          ·
            refine ⟨39951078408418392024761827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213072418178231424132063077 39951078408418392024761827)
            ·
              refine ⟨59926617612627588037142741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39951078408418392024761827 59926617612627588037142741)
              ·
                refine ⟨1404530100295959094620533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59926617612627588037142741 1404530100295959094620533)
                ·
                  refine ⟨131674696902746165120675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1404530100295959094620533 131674696902746165120675)
                  ·
                    rfl

theorem cell23_2307920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 5].length) (baseStart_2307920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307920 prefixEnd_2307920 := by exact prefixLift 2307920
  have htrace : WordTrace (prefixWord ++ tailWord_2307920) baseStart_2307920 baseEnd_2307920 := by
    simpa [prefixWord, tailWord_2307920, baseEnd_2307920] using wordTrace_append hprefix tailTrace_2307920
  have hstable : (prefixWord ++ tailWord_2307920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307920).length < 2 ^ (prefixWord ++ tailWord_2307920).sum := by decide
  have hdescent : baseEnd_2307920 < baseStart_2307920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307930 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_2307930 : Nat := 118140960795 + 2307930 * 2 ^ 59
def prefixEnd_2307930 : Nat := 4983230072969 + 3 ^ 40 * 2307930 * 2
def baseEnd_2307930 : Nat := 1185077406931260446961029

theorem tailTrace_2307930 : CollatzResearch.WordTrace tailWord_2307930 prefixEnd_2307930 1185077406931260446961029 := by
  unfold tailWord_2307930
  simp only [CollatzResearch.WordTrace]
  refine ⟨21044280632192811977046311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56118081685847498605456829 21044280632192811977046311)
  ·
    refine ⟨31566420948289217965569467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21044280632192811977046311 31566420948289217965569467)
    ·
      refine ⟨47349631422433826948354201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31566420948289217965569467 47349631422433826948354201)
      ·
        refine ⟨35512223566825370211265651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47349631422433826948354201 35512223566825370211265651)
        ·
          refine ⟨53268335350238055316898477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35512223566825370211265651 53268335350238055316898477)
          ·
            refine ⟨19975625756339270743836929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53268335350238055316898477 19975625756339270743836929)
            ·
              refine ⟨14981719317254453057877697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19975625756339270743836929 14981719317254453057877697)
              ·
                refine ⟨11236289487940839793408273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14981719317254453057877697 11236289487940839793408273)
                ·
                  refine ⟨8427217115955629845056205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11236289487940839793408273 8427217115955629845056205)
                  ·
                    refine ⟨3160206418483361191896077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8427217115955629845056205 3160206418483361191896077)
                    ·
                      refine ⟨1185077406931260446961029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3160206418483361191896077 1185077406931260446961029)
                      ·
                        rfl

theorem cell23_2307930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_2307930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307930 prefixEnd_2307930 := by exact prefixLift 2307930
  have htrace : WordTrace (prefixWord ++ tailWord_2307930) baseStart_2307930 baseEnd_2307930 := by
    simpa [prefixWord, tailWord_2307930, baseEnd_2307930] using wordTrace_append hprefix tailTrace_2307930
  have hstable : (prefixWord ++ tailWord_2307930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307930).length < 2 ^ (prefixWord ++ tailWord_2307930).sum := by decide
  have hdescent : baseEnd_2307930 < baseStart_2307930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307957 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_2307957 : Nat := 118140960795 + 2307957 * 2 ^ 59
def prefixEnd_2307957 : Nat := 4983230072969 + 3 ^ 40 * 2307957 * 2
def baseEnd_2307957 : Nat := 1185091270908931841323405

theorem tailTrace_2307957 : CollatzResearch.WordTrace tailWord_2307957 prefixEnd_2307957 1185091270908931841323405 := by
  unfold tailWord_2307957
  simp only [CollatzResearch.WordTrace]
  refine ⟨84178107299673431519418125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56118738199782287679612083 84178107299673431519418125)
  ·
    refine ⟨31566790237377536819781797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84178107299673431519418125 31566790237377536819781797)
    ·
      refine ⟨5918773169508288153709087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31566790237377536819781797 5918773169508288153709087)
      ·
        refine ⟨8878159754262432230563631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918773169508288153709087 8878159754262432230563631)
        ·
          refine ⟨13317239631393648345845447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8878159754262432230563631 13317239631393648345845447)
          ·
            refine ⟨19975859447090472518768171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13317239631393648345845447 19975859447090472518768171)
            ·
              refine ⟨29963789170635708778152257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19975859447090472518768171 29963789170635708778152257)
              ·
                refine ⟨22472841877976781583614193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29963789170635708778152257 22472841877976781583614193)
                ·
                  refine ⟨16854631408482586187710645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22472841877976781583614193 16854631408482586187710645)
                  ·
                    refine ⟨1580121694545242455097873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16854631408482586187710645 1580121694545242455097873)
                    ·
                      refine ⟨1185091270908931841323405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580121694545242455097873 1185091270908931841323405)
                      ·
                        rfl

theorem cell23_2307957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_2307957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307957 prefixEnd_2307957 := by exact prefixLift 2307957
  have htrace : WordTrace (prefixWord ++ tailWord_2307957) baseStart_2307957 baseEnd_2307957 := by
    simpa [prefixWord, tailWord_2307957, baseEnd_2307957] using wordTrace_append hprefix tailTrace_2307957
  have hstable : (prefixWord ++ tailWord_2307957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307957).length < 2 ^ (prefixWord ++ tailWord_2307957).sum := by decide
  have hdescent : baseEnd_2307957 < baseStart_2307957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307980 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_2307980 : Nat := 118140960795 + 2307980 * 2 ^ 59
def prefixEnd_2307980 : Nat := 4983230072969 + 3 ^ 40 * 2307980 * 2
def baseEnd_2307980 : Nat := 395034360321328417111933

theorem tailTrace_2307980 : CollatzResearch.WordTrace tailWord_2307980 prefixEnd_2307980 395034360321328417111933 := by
  unfold tailWord_2307980
  simp only [CollatzResearch.WordTrace]
  refine ⟨42089473089295053223752697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56119297452393404298336929 42089473089295053223752697)
  ·
    refine ⟨31567104816971289917814523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42089473089295053223752697 31567104816971289917814523)
    ·
      refine ⟨47350657225456934876721785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31567104816971289917814523 47350657225456934876721785)
      ·
        refine ⟨35512992919092701157541339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47350657225456934876721785 35512992919092701157541339)
        ·
          refine ⟨53269489378639051736312009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35512992919092701157541339 53269489378639051736312009)
          ·
            refine ⟨39952117033979288802234007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53269489378639051736312009 39952117033979288802234007)
            ·
              refine ⟨59928175550968933203351011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39952117033979288802234007 59928175550968933203351011)
              ·
                refine ⟨89892263326453399805026517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59928175550968933203351011 89892263326453399805026517)
                ·
                  refine ⟨2106849921713751557930309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 89892263326453399805026517 2106849921713751557930309)
                  ·
                    refine ⟨395034360321328417111933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2106849921713751557930309 395034360321328417111933)
                    ·
                      rfl

theorem cell23_2307980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_2307980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307980 prefixEnd_2307980 := by exact prefixLift 2307980
  have htrace : WordTrace (prefixWord ++ tailWord_2307980) baseStart_2307980 baseEnd_2307980 := by
    simpa [prefixWord, tailWord_2307980, baseEnd_2307980] using wordTrace_append hprefix tailTrace_2307980
  have hstable : (prefixWord ++ tailWord_2307980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307980).length < 2 ^ (prefixWord ++ tailWord_2307980).sum := by decide
  have hdescent : baseEnd_2307980 < baseStart_2307980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307997 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_2307997 : Nat := 118140960795 + 2307997 * 2 ^ 59
def prefixEnd_2307997 : Nat := 4983230072969 + 3 ^ 40 * 2307997 * 2
def baseEnd_2307997 : Nat := 395037270045037228274407

theorem tailTrace_2307997 : CollatzResearch.WordTrace tailWord_2307997 prefixEnd_2307997 395037270045037228274407 := by
  unfold tailWord_2307997
  simp only [CollatzResearch.WordTrace]
  refine ⟨84179566219528518350874245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56119710813019012233916163 84179566219528518350874245)
  ·
    refine ⟨15783668666161597190788921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84179566219528518350874245 15783668666161597190788921)
    ·
      refine ⟨11837751499621197893091691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15783668666161597190788921 11837751499621197893091691)
      ·
        refine ⟨17756627249431796839637537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11837751499621197893091691 17756627249431796839637537)
        ·
          refine ⟨13317470437073847629728153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17756627249431796839637537 13317470437073847629728153)
          ·
            refine ⟨9988102827805385722296115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13317470437073847629728153 9988102827805385722296115)
            ·
              refine ⟨14982154241708078583444173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9988102827805385722296115 14982154241708078583444173)
              ·
                refine ⟨5618307840640529468791565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14982154241708078583444173 5618307840640529468791565)
                ·
                  refine ⟨2106865440240198550796837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5618307840640529468791565 2106865440240198550796837)
                  ·
                    refine ⟨395037270045037228274407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2106865440240198550796837 395037270045037228274407)
                    ·
                      rfl

theorem cell23_2307997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_2307997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2307997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2307997 prefixEnd_2307997 := by exact prefixLift 2307997
  have htrace : WordTrace (prefixWord ++ tailWord_2307997) baseStart_2307997 baseEnd_2307997 := by
    simpa [prefixWord, tailWord_2307997, baseEnd_2307997] using wordTrace_append hprefix tailTrace_2307997
  have hstable : (prefixWord ++ tailWord_2307997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307997).length < 2 ^ (prefixWord ++ tailWord_2307997).sum := by decide
  have hdescent : baseEnd_2307997 < baseStart_2307997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308007 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2308007 : Nat := 118140960795 + 2308007 * 2 ^ 59
def prefixEnd_2308007 : Nat := 4983230072969 + 3 ^ 40 * 2308007 * 2
def baseEnd_2308007 : Nat := 1185116944941656645698175

theorem tailTrace_2308007 : CollatzResearch.WordTrace tailWord_2308007 prefixEnd_2308007 1185116944941656645698175 := by
  unfold tailWord_2308007
  simp only [CollatzResearch.WordTrace]
  refine ⟨84179930949492290058738275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56119953966328193372492183 84179930949492290058738275)
  ·
    refine ⟨126269896424238435088107413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84179930949492290058738275 126269896424238435088107413)
    ·
      refine ⟨5918901394886176644755035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126269896424238435088107413 5918901394886176644755035)
      ·
        refine ⟨8878352092329264967132553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918901394886176644755035 8878352092329264967132553)
        ·
          refine ⟨6658764069246948725349415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8878352092329264967132553 6658764069246948725349415)
          ·
            refine ⟨9988146103870423088024123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658764069246948725349415 9988146103870423088024123)
            ·
              refine ⟨14982219155805634632036185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9988146103870423088024123 14982219155805634632036185)
              ·
                refine ⟨11236664366854225974027139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14982219155805634632036185 11236664366854225974027139)
                ·
                  refine ⟨16854996550281338961040709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11236664366854225974027139 16854996550281338961040709)
                  ·
                    refine ⟨3160311853177751055195133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16854996550281338961040709 3160311853177751055195133)
                    ·
                      refine ⟨1185116944941656645698175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3160311853177751055195133 1185116944941656645698175)
                      ·
                        rfl

theorem cell23_2308007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2308007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308007 prefixEnd_2308007 := by exact prefixLift 2308007
  have htrace : WordTrace (prefixWord ++ tailWord_2308007) baseStart_2308007 baseEnd_2308007 := by
    simpa [prefixWord, tailWord_2308007, baseEnd_2308007] using wordTrace_append hprefix tailTrace_2308007
  have hstable : (prefixWord ++ tailWord_2308007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308007).length < 2 ^ (prefixWord ++ tailWord_2308007).sum := by decide
  have hdescent : baseEnd_2308007 < baseStart_2308007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308061 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 6]
def baseStart_2308061 : Nat := 118140960795 + 2308061 * 2 ^ 59
def prefixEnd_2308061 : Nat := 4983230072969 + 3 ^ 40 * 2308061 * 2
def baseEnd_2308061 : Nat := 131682741432999937158103

theorem tailTrace_2308061 : CollatzResearch.WordTrace tailWord_2308061 prefixEnd_2308061 131682741432999937158103 := by
  unfold tailWord_2308061
  simp only [CollatzResearch.WordTrace]
  refine ⟨84181900491296657281204037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56121266994197771520802691 84181900491296657281204037)
  ·
    refine ⟨15784106342118123240225757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84181900491296657281204037 15784106342118123240225757)
    ·
      refine ⟨5919039878294296215084659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15784106342118123240225757 5919039878294296215084659)
      ·
        refine ⟨8878559817441444322626989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5919039878294296215084659 8878559817441444322626989)
        ·
          refine ⟨3329459931540541620985121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8878559817441444322626989 3329459931540541620985121)
          ·
            refine ⟨2497094948655406215738841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3329459931540541620985121 2497094948655406215738841)
            ·
              refine ⟨1872821211491554661804131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497094948655406215738841 1872821211491554661804131)
              ·
                refine ⟨2809231817237331992706197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872821211491554661804131 2809231817237331992706197)
                ·
                  refine ⟨131682741432999937158103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2809231817237331992706197 131682741432999937158103)
                  ·
                    rfl

theorem cell23_2308061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_2308061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308061 prefixEnd_2308061 := by exact prefixLift 2308061
  have htrace : WordTrace (prefixWord ++ tailWord_2308061) baseStart_2308061 baseEnd_2308061 := by
    simpa [prefixWord, tailWord_2308061, baseEnd_2308061] using wordTrace_append hprefix tailTrace_2308061
  have hstable : (prefixWord ++ tailWord_2308061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308061).length < 2 ^ (prefixWord ++ tailWord_2308061).sum := by decide
  have hdescent : baseEnd_2308061 < baseStart_2308061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308080 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_2308080 : Nat := 118140960795 + 2308080 * 2 ^ 59
def prefixEnd_2308080 : Nat := 4983230072969 + 3 ^ 40 * 2308080 * 2
def baseEnd_2308080 : Nat := 1185154429029434860085339

theorem tailTrace_2308080 : CollatzResearch.WordTrace tailWord_2308080 prefixEnd_2308080 1185154429029434860085339 := by
  unfold tailWord_2308080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42091296739113911763072847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56121728985485215684097129 42091296739113911763072847)
  ·
    refine ⟨63136945108670867644609271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42091296739113911763072847 63136945108670867644609271)
    ·
      refine ⟨94705417663006301466913907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63136945108670867644609271 94705417663006301466913907)
      ·
        refine ⟨142058126494509452200370861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94705417663006301466913907 142058126494509452200370861)
        ·
          refine ⟨53271797435441044575139073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142058126494509452200370861 53271797435441044575139073)
          ·
            refine ⟨39953848076580783431354305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53271797435441044575139073 39953848076580783431354305)
            ·
              refine ⟨29965386057435587573515729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39953848076580783431354305 29965386057435587573515729)
              ·
                refine ⟨22474039543076690680136797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29965386057435587573515729 22474039543076690680136797)
                ·
                  refine ⟨8427764828653759005051299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22474039543076690680136797 8427764828653759005051299)
                  ·
                    refine ⟨12641647242980638507576949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8427764828653759005051299 12641647242980638507576949)
                    ·
                      refine ⟨1185154429029434860085339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12641647242980638507576949 1185154429029434860085339)
                      ·
                        rfl

theorem cell23_2308080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_2308080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308080 prefixEnd_2308080 := by exact prefixLift 2308080
  have htrace : WordTrace (prefixWord ++ tailWord_2308080) baseStart_2308080 baseEnd_2308080 := by
    simpa [prefixWord, tailWord_2308080, baseEnd_2308080] using wordTrace_append hprefix tailTrace_2308080
  have hstable : (prefixWord ++ tailWord_2308080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308080).length < 2 ^ (prefixWord ++ tailWord_2308080).sum := by decide
  have hdescent : baseEnd_2308080 < baseStart_2308080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308081 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 2, 3, 2]
def baseStart_2308081 : Nat := 118140960795 + 2308081 * 2 ^ 59
def prefixEnd_2308081 : Nat := 4983230072969 + 3 ^ 40 * 2308081 * 2
def baseEnd_2308081 : Nat := 1185154942510089356172835

theorem tailTrace_2308081 : CollatzResearch.WordTrace tailWord_2308081 prefixEnd_2308081 1185154942510089356172835 := by
  unfold tailWord_2308081
  simp only [CollatzResearch.WordTrace]
  refine ⟨84182629951224200696932097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56121753300816133797954731 84182629951224200696932097)
  ·
    refine ⟨63136972463418150522699073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84182629951224200696932097 63136972463418150522699073)
    ·
      refine ⟨47352729347563612892024305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63136972463418150522699073 47352729347563612892024305)
      ·
        refine ⟨35514547010672709669018229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47352729347563612892024305 35514547010672709669018229)
        ·
          refine ⟨3329488782250566531470459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35514547010672709669018229 3329488782250566531470459)
          ·
            refine ⟨4994233173375849797205689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329488782250566531470459 4994233173375849797205689)
            ·
              refine ⟨3745674880031887347904267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4994233173375849797205689 3745674880031887347904267)
              ·
                refine ⟨5618512320047831021856401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3745674880031887347904267 5618512320047831021856401)
                ·
                  refine ⟨4213884240035873266392301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5618512320047831021856401 4213884240035873266392301)
                  ·
                    refine ⟨1580206590013452474897113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4213884240035873266392301 1580206590013452474897113)
                    ·
                      refine ⟨1185154942510089356172835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580206590013452474897113 1185154942510089356172835)
                      ·
                        rfl

theorem cell23_2308081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_2308081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308081 prefixEnd_2308081 := by exact prefixLift 2308081
  have htrace : WordTrace (prefixWord ++ tailWord_2308081) baseStart_2308081 baseEnd_2308081 := by
    simpa [prefixWord, tailWord_2308081, baseEnd_2308081] using wordTrace_append hprefix tailTrace_2308081
  have hstable : (prefixWord ++ tailWord_2308081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308081).length < 2 ^ (prefixWord ++ tailWord_2308081).sum := by decide
  have hdescent : baseEnd_2308081 < baseStart_2308081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308104 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 2, 4]
def baseStart_2308104 : Nat := 118140960795 + 2308104 * 2 ^ 59
def prefixEnd_2308104 : Nat := 4983230072969 + 3 ^ 40 * 2308104 * 2
def baseEnd_2308104 : Nat := 395055584188380922061743

theorem tailTrace_2308104 : CollatzResearch.WordTrace tailWord_2308104 prefixEnd_2308104 395055584188380922061743 := by
  unfold tailWord_2308104
  simp only [CollatzResearch.WordTrace]
  refine ⟨42091734415070437812509683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56122312553427250416679577 42091734415070437812509683)
  ·
    refine ⟨63137601622605656718764525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42091734415070437812509683 63137601622605656718764525)
    ·
      refine ⟨23676600608477121269536697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63137601622605656718764525 23676600608477121269536697)
      ·
        refine ⟨17757450456357840952152523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23676600608477121269536697 17757450456357840952152523)
        ·
          refine ⟨26636175684536761428228785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17757450456357840952152523 26636175684536761428228785)
          ·
            refine ⟨19977131763402571071171589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26636175684536761428228785 19977131763402571071171589)
            ·
              refine ⟨3745712205637982075844673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19977131763402571071171589 3745712205637982075844673)
              ·
                refine ⟨2809284154228486556883505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3745712205637982075844673 2809284154228486556883505)
                ·
                  refine ⟨2106963115671364917662629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2809284154228486556883505 2106963115671364917662629)
                  ·
                    refine ⟨395055584188380922061743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2106963115671364917662629 395055584188380922061743)
                    ·
                      rfl

theorem cell23_2308104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_2308104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308104 prefixEnd_2308104 := by exact prefixLift 2308104
  have htrace : WordTrace (prefixWord ++ tailWord_2308104) baseStart_2308104 baseEnd_2308104 := by
    simpa [prefixWord, tailWord_2308104, baseEnd_2308104] using wordTrace_append hprefix tailTrace_2308104
  have hstable : (prefixWord ++ tailWord_2308104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308104).length < 2 ^ (prefixWord ++ tailWord_2308104).sum := by decide
  have hdescent : baseEnd_2308104 < baseStart_2308104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308124 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_2308124 : Nat := 118140960795 + 2308124 * 2 ^ 59
def prefixEnd_2308124 : Nat := 4983230072969 + 3 ^ 40 * 2308124 * 2
def baseEnd_2308124 : Nat := 1185177022178232687935137

theorem tailTrace_2308124 : CollatzResearch.WordTrace tailWord_2308124 prefixEnd_2308124 1185177022178232687935137 := by
  unfold tailWord_2308124
  simp only [CollatzResearch.WordTrace]
  refine ⟨42092099145034209520373713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56122798860045612693831617 42092099145034209520373713)
  ·
    refine ⟨31569074358775657140280285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42092099145034209520373713 31569074358775657140280285)
    ·
      refine ⟨11838402884540871427605107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31569074358775657140280285 11838402884540871427605107)
      ·
        refine ⟨17757604326811307141407661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11838402884540871427605107 17757604326811307141407661)
        ·
          refine ⟨6659101622554240178027873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17757604326811307141407661 6659101622554240178027873)
          ·
            refine ⟨4994326216915680133520905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6659101622554240178027873 4994326216915680133520905)
            ·
              refine ⟨3745744662686760100140679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4994326216915680133520905 3745744662686760100140679)
              ·
                refine ⟨5618616994030140150211019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3745744662686760100140679 5618616994030140150211019)
                ·
                  refine ⟨8427925491045210225316529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5618616994030140150211019 8427925491045210225316529)
                  ·
                    refine ⟨6320944118283907668987397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8427925491045210225316529 6320944118283907668987397)
                    ·
                      refine ⟨1185177022178232687935137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6320944118283907668987397 1185177022178232687935137)
                      ·
                        rfl

theorem cell23_2308124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_2308124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308124 prefixEnd_2308124 := by exact prefixLift 2308124
  have htrace : WordTrace (prefixWord ++ tailWord_2308124) baseStart_2308124 baseEnd_2308124 := by
    simpa [prefixWord, tailWord_2308124, baseEnd_2308124] using wordTrace_append hprefix tailTrace_2308124
  have hstable : (prefixWord ++ tailWord_2308124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308124).length < 2 ^ (prefixWord ++ tailWord_2308124).sum := by decide
  have hdescent : baseEnd_2308124 < baseStart_2308124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308148 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2308148 : Nat := 118140960795 + 2308148 * 2 ^ 59
def prefixEnd_2308148 : Nat := 4983230072969 + 3 ^ 40 * 2308148 * 2
def baseEnd_2308148 : Nat := 1185189345713940594035027

theorem tailTrace_2308148 : CollatzResearch.WordTrace tailWord_2308148 prefixEnd_2308148 1185189345713940594035027 := by
  unfold tailWord_2308148
  simp only [CollatzResearch.WordTrace]
  refine ⟨42092536820990735569810549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56123382427987647426414065 42092536820990735569810549)
  ·
    refine ⟨3946175326967881459669739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42092536820990735569810549 3946175326967881459669739)
    ·
      refine ⟨5919262990451822189504609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3946175326967881459669739 5919262990451822189504609)
      ·
        refine ⟨4439447242838866642128457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5919262990451822189504609 4439447242838866642128457)
        ·
          refine ⟨3329585432129149981596343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4439447242838866642128457 3329585432129149981596343)
          ·
            refine ⟨4994378148193724972394515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329585432129149981596343 4994378148193724972394515)
            ·
              refine ⟨7491567222290587458591773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4994378148193724972394515 7491567222290587458591773)
              ·
                refine ⟨2809337708358970296971915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7491567222290587458591773 2809337708358970296971915)
                ·
                  refine ⟨4214006562538455445457873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809337708358970296971915 4214006562538455445457873)
                  ·
                    refine ⟨3160504921903841584093405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4214006562538455445457873 3160504921903841584093405)
                    ·
                      refine ⟨1185189345713940594035027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3160504921903841584093405 1185189345713940594035027)
                      ·
                        rfl

theorem cell23_2308148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2308148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308148 prefixEnd_2308148 := by exact prefixLift 2308148
  have htrace : WordTrace (prefixWord ++ tailWord_2308148) baseStart_2308148 baseEnd_2308148 := by
    simpa [prefixWord, tailWord_2308148, baseEnd_2308148] using wordTrace_append hprefix tailTrace_2308148
  have hstable : (prefixWord ++ tailWord_2308148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308148).length < 2 ^ (prefixWord ++ tailWord_2308148).sum := by decide
  have hdescent : baseEnd_2308148 < baseStart_2308148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308161 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2308161 : Nat := 118140960795 + 2308161 * 2 ^ 59
def prefixEnd_2308161 : Nat := 4983230072969 + 3 ^ 40 * 2308161 * 2
def baseEnd_2308161 : Nat := 1185196020962449043172467

theorem tailTrace_2308161 : CollatzResearch.WordTrace tailWord_2308161 prefixEnd_2308161 1185196020962449043172467 := by
  unfold tailWord_2308161
  simp only [CollatzResearch.WordTrace]
  refine ⟨84185547790934374359844337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56123698527289582906562891 84185547790934374359844337)
  ·
    refine ⟨63139160843200780769883253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84185547790934374359844337 63139160843200780769883253)
    ·
      refine ⟨5919296329050073197176555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63139160843200780769883253 5919296329050073197176555)
      ·
        refine ⟨8878944493575109795764833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5919296329050073197176555 8878944493575109795764833)
        ·
          refine ⟨6659208370181332346823625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8878944493575109795764833 6659208370181332346823625)
          ·
            refine ⟨4994406277635999260117719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6659208370181332346823625 4994406277635999260117719)
            ·
              refine ⟨7491609416453998890176579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4994406277635999260117719 7491609416453998890176579)
              ·
                refine ⟨11237414124680998335264869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7491609416453998890176579 11237414124680998335264869)
                ·
                  refine ⟨2107015148377687187862163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11237414124680998335264869 2107015148377687187862163)
                  ·
                    refine ⟨3160522722566530781793245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2107015148377687187862163 3160522722566530781793245)
                    ·
                      refine ⟨1185196020962449043172467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3160522722566530781793245 1185196020962449043172467)
                      ·
                        rfl

theorem cell23_2308161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2308161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308161 prefixEnd_2308161 := by exact prefixLift 2308161
  have htrace : WordTrace (prefixWord ++ tailWord_2308161) baseStart_2308161 baseEnd_2308161 := by
    simpa [prefixWord, tailWord_2308161, baseEnd_2308161] using wordTrace_append hprefix tailTrace_2308161
  have hstable : (prefixWord ++ tailWord_2308161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308161).length < 2 ^ (prefixWord ++ tailWord_2308161).sum := by decide
  have hdescent : baseEnd_2308161 < baseStart_2308161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308178 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_2308178 : Nat := 118140960795 + 2308178 * 2 ^ 59
def prefixEnd_2308178 : Nat := 4983230072969 + 3 ^ 40 * 2308178 * 2
def baseEnd_2308178 : Nat := 1185204750133575476659889

theorem tailTrace_2308178 : CollatzResearch.WordTrace tailWord_2308178 prefixEnd_2308178 1185204750133575476659889 := by
  unfold tailWord_2308178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21046541957968196565803297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56124111887915190842142125 21046541957968196565803297)
  ·
    refine ⟨15784906468476147424352473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21046541957968196565803297 15784906468476147424352473)
    ·
      refine ⟨11838679851357110568264355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15784906468476147424352473 11838679851357110568264355)
      ·
        refine ⟨17758019777035665852396533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11838679851357110568264355 17758019777035665852396533)
        ·
          refine ⟨1664814354097093673662175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17758019777035665852396533 1664814354097093673662175)
          ·
            refine ⟨2497221531145640510493263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664814354097093673662175 2497221531145640510493263)
            ·
              refine ⟨3745832296718460765739895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497221531145640510493263 3745832296718460765739895)
              ·
                refine ⟨5618748445077691148609843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3745832296718460765739895 5618748445077691148609843)
                ·
                  refine ⟨8428122667616536722914765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5618748445077691148609843 8428122667616536722914765)
                  ·
                    refine ⟨3160546000356201271093037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8428122667616536722914765 3160546000356201271093037)
                    ·
                      refine ⟨1185204750133575476659889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3160546000356201271093037 1185204750133575476659889)
                      ·
                        rfl

theorem cell23_2308178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_2308178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308178 prefixEnd_2308178 := by exact prefixLift 2308178
  have htrace : WordTrace (prefixWord ++ tailWord_2308178) baseStart_2308178 baseEnd_2308178 := by
    simpa [prefixWord, tailWord_2308178, baseEnd_2308178] using wordTrace_append hprefix tailTrace_2308178
  have hstable : (prefixWord ++ tailWord_2308178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308178).length < 2 ^ (prefixWord ++ tailWord_2308178).sum := by decide
  have hdescent : baseEnd_2308178 < baseStart_2308178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308188 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_2308188 : Nat := 118140960795 + 2308188 * 2 ^ 59
def prefixEnd_2308188 : Nat := 4983230072969 + 3 ^ 40 * 2308188 * 2
def baseEnd_2308188 : Nat := 1185209884940120437534843

theorem tailTrace_2308188 : CollatzResearch.WordTrace tailWord_2308188 prefixEnd_2308188 1185209884940120437534843 := by
  unfold tailWord_2308188
  simp only [CollatzResearch.WordTrace]
  refine ⟨42093266280918278985538609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56124355041224371980718145 42093266280918278985538609)
  ·
    refine ⟨31569949710688709239153957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42093266280918278985538609 31569949710688709239153957)
    ·
      refine ⟨5919365570754132982341367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31569949710688709239153957 5919365570754132982341367)
      ·
        refine ⟨8879048356131199473512051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5919365570754132982341367 8879048356131199473512051)
        ·
          refine ⟨13318572534196799210268077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8879048356131199473512051 13318572534196799210268077)
          ·
            refine ⟨4994464700323799703850529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13318572534196799210268077 4994464700323799703850529)
            ·
              refine ⟨3745848525242849777887897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4994464700323799703850529 3745848525242849777887897)
              ·
                refine ⟨2809386393932137333415923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3745848525242849777887897 2809386393932137333415923)
                ·
                  refine ⟨4214079590898206000123885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809386393932137333415923 4214079590898206000123885)
                  ·
                    refine ⟨1580279846586827250046457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4214079590898206000123885 1580279846586827250046457)
                    ·
                      refine ⟨1185209884940120437534843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580279846586827250046457 1185209884940120437534843)
                      ·
                        rfl

theorem cell23_2308188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_2308188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308188 prefixEnd_2308188 := by exact prefixLift 2308188
  have htrace : WordTrace (prefixWord ++ tailWord_2308188) baseStart_2308188 baseEnd_2308188 := by
    simpa [prefixWord, tailWord_2308188, baseEnd_2308188] using wordTrace_append hprefix tailTrace_2308188
  have hstable : (prefixWord ++ tailWord_2308188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308188).length < 2 ^ (prefixWord ++ tailWord_2308188).sum := by decide
  have hdescent : baseEnd_2308188 < baseStart_2308188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308274 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2308274 : Nat := 118140960795 + 2308274 * 2 ^ 59
def prefixEnd_2308274 : Nat := 4983230072969 + 3 ^ 40 * 2308274 * 2
def baseEnd_2308274 : Nat := 1185254044276407101059447

theorem tailTrace_2308274 : CollatzResearch.WordTrace tailWord_2308274 prefixEnd_2308274 1185254044276407101059447 := by
  unfold tailWord_2308274
  simp only [CollatzResearch.WordTrace]
  refine ⟨21047417309881248664676969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56126446159683329772471917 21047417309881248664676969)
  ·
    refine ⟨15785562982410936498507727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21047417309881248664676969 15785562982410936498507727)
    ·
      refine ⟨23678344473616404747761591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15785562982410936498507727 23678344473616404747761591)
      ·
        refine ⟨35517516710424607121642387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23678344473616404747761591 35517516710424607121642387)
        ·
          refine ⟨53276275065636910682463581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35517516710424607121642387 53276275065636910682463581)
          ·
            refine ⟨19978603149613841505923843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53276275065636910682463581 19978603149613841505923843)
            ·
              refine ⟨29967904724420762258885765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19978603149613841505923843 29967904724420762258885765)
              ·
                refine ⟨5618982135828892923541081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29967904724420762258885765 5618982135828892923541081)
                ·
                  refine ⟨4214236601871669692655811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5618982135828892923541081 4214236601871669692655811)
                  ·
                    refine ⟨6321354902807504538983717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4214236601871669692655811 6321354902807504538983717)
                    ·
                      refine ⟨1185254044276407101059447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6321354902807504538983717 1185254044276407101059447)
                      ·
                        rfl

theorem cell23_2308274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2308274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308274 prefixEnd_2308274 := by exact prefixLift 2308274
  have htrace : WordTrace (prefixWord ++ tailWord_2308274) baseStart_2308274 baseEnd_2308274 := by
    simpa [prefixWord, tailWord_2308274, baseEnd_2308274] using wordTrace_append hprefix tailTrace_2308274
  have hstable : (prefixWord ++ tailWord_2308274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308274).length < 2 ^ (prefixWord ++ tailWord_2308274).sum := by decide
  have hdescent : baseEnd_2308274 < baseStart_2308274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308287 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_2308287 : Nat := 118140960795 + 2308287 * 2 ^ 59
def prefixEnd_2308287 : Nat := 4983230072969 + 3 ^ 40 * 2308287 * 2
def baseEnd_2308287 : Nat := 1185260719524915550196887

theorem tailTrace_2308287 : CollatzResearch.WordTrace tailWord_2308287 prefixEnd_2308287 1185260719524915550196887 := by
  unfold tailWord_2308287
  simp only [CollatzResearch.WordTrace]
  refine ⟨84190143388477897878931115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56126762258985265252620743 84190143388477897878931115)
  ·
    refine ⟨126285215082716846818396673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84190143388477897878931115 126285215082716846818396673)
    ·
      refine ⟨94713911312037635113797505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126285215082716846818396673 94713911312037635113797505)
      ·
        refine ⟨71035433484028226335348129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94713911312037635113797505 71035433484028226335348129)
        ·
          refine ⟨53276575113021169751511097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71035433484028226335348129 53276575113021169751511097)
          ·
            refine ⟨39957431334765877313633323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53276575113021169751511097 39957431334765877313633323)
            ·
              refine ⟨59936147002148815970449985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39957431334765877313633323 59936147002148815970449985)
              ·
                refine ⟨44952110251611611977837489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59936147002148815970449985 44952110251611611977837489)
                ·
                  refine ⟨33714082688708708983378117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44952110251611611977837489 33714082688708708983378117)
                  ·
                    refine ⟨6321390504132882934383397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33714082688708708983378117 6321390504132882934383397)
                    ·
                      refine ⟨1185260719524915550196887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6321390504132882934383397 1185260719524915550196887)
                      ·
                        rfl

theorem cell23_2308287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_2308287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308287 prefixEnd_2308287 := by exact prefixLift 2308287
  have htrace : WordTrace (prefixWord ++ tailWord_2308287) baseStart_2308287 baseEnd_2308287 := by
    simpa [prefixWord, tailWord_2308287, baseEnd_2308287] using wordTrace_append hprefix tailTrace_2308287
  have hstable : (prefixWord ++ tailWord_2308287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308287).length < 2 ^ (prefixWord ++ tailWord_2308287).sum := by decide
  have hdescent : baseEnd_2308287 < baseStart_2308287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308361 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 1, 5]
def baseStart_2308361 : Nat := 118140960795 + 2308361 * 2 ^ 59
def prefixEnd_2308361 : Nat := 4983230072969 + 3 ^ 40 * 2308361 * 2
def baseEnd_2308361 : Nat := 395099572364449420223849

theorem tailTrace_2308361 : CollatzResearch.WordTrace tailWord_2308361 prefixEnd_2308361 395099572364449420223849 := by
  unfold tailWord_2308361
  simp only [CollatzResearch.WordTrace]
  refine ⟨84192842390209808517124937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56128561593473205678083291 84192842390209808517124937)
  ·
    refine ⟨63144631792657356387843703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84192842390209808517124937 63144631792657356387843703)
    ·
      refine ⟨94716947688986034581765555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63144631792657356387843703 94716947688986034581765555)
      ·
        refine ⟨142075421533479051872648333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94716947688986034581765555 142075421533479051872648333)
        ·
          refine ⟨53278283075054644452243125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142075421533479051872648333 53278283075054644452243125)
          ·
            refine ⟨4994839038286372917397793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53278283075054644452243125 4994839038286372917397793)
            ·
              refine ⟨3746129278714779688048345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4994839038286372917397793 3746129278714779688048345)
              ·
                refine ⟨2809596959036084766036259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3746129278714779688048345 2809596959036084766036259)
                ·
                  refine ⟨4214395438554127149054389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809596959036084766036259 4214395438554127149054389)
                  ·
                    refine ⟨395099572364449420223849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4214395438554127149054389 395099572364449420223849)
                    ·
                      rfl

theorem cell23_2308361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_2308361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308361 prefixEnd_2308361 := by exact prefixLift 2308361
  have htrace : WordTrace (prefixWord ++ tailWord_2308361) baseStart_2308361 baseEnd_2308361 := by
    simpa [prefixWord, tailWord_2308361, baseEnd_2308361] using wordTrace_append hprefix tailTrace_2308361
  have hstable : (prefixWord ++ tailWord_2308361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308361).length < 2 ^ (prefixWord ++ tailWord_2308361).sum := by decide
  have hdescent : baseEnd_2308361 < baseStart_2308361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308375 : List Nat := [1, 1, 3, 4, 1, 2, 3, 3, 1, 1, 3]
def baseStart_2308375 : Nat := 118140960795 + 2308375 * 2 ^ 59
def prefixEnd_2308375 : Nat := 4983230072969 + 3 ^ 40 * 2308375 * 2
def baseEnd_2308375 : Nat := 1185305905822511205896483

theorem tailTrace_2308375 : CollatzResearch.WordTrace tailWord_2308375 prefixEnd_2308375 1185305905822511205896483 := by
  unfold tailWord_2308375
  simp only [CollatzResearch.WordTrace]
  refine ⟨84193353012159088908134579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56128902008106059272089719 84193353012159088908134579)
  ·
    refine ⟨126290029518238633362201869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84193353012159088908134579 126290029518238633362201869)
    ·
      refine ⟨47358761069339487510825701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126290029518238633362201869 47358761069339487510825701)
      ·
        refine ⟨8879767700501153908279819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47358761069339487510825701 8879767700501153908279819)
        ·
          refine ⟨13319651550751730862419729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8879767700501153908279819 13319651550751730862419729)
          ·
            refine ⟨9989738663063798146814797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13319651550751730862419729 9989738663063798146814797)
            ·
              refine ⟨3746151998648924305055549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9989738663063798146814797 3746151998648924305055549)
              ·
                refine ⟨1404806999493346614395831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3746151998648924305055549 1404806999493346614395831)
                ·
                  refine ⟨2107210499240019921593747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404806999493346614395831 2107210499240019921593747)
                  ·
                    refine ⟨3160815748860029882390621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2107210499240019921593747 3160815748860029882390621)
                    ·
                      refine ⟨1185305905822511205896483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3160815748860029882390621 1185305905822511205896483)
                      ·
                        rfl

theorem cell23_2308375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_2308375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308375 prefixEnd_2308375 := by exact prefixLift 2308375
  have htrace : WordTrace (prefixWord ++ tailWord_2308375) baseStart_2308375 baseEnd_2308375 := by
    simpa [prefixWord, tailWord_2308375, baseEnd_2308375] using wordTrace_append hprefix tailTrace_2308375
  have hstable : (prefixWord ++ tailWord_2308375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308375).length < 2 ^ (prefixWord ++ tailWord_2308375).sum := by decide
  have hdescent : baseEnd_2308375 < baseStart_2308375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308392 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_2308392 : Nat := 118140960795 + 2308392 * 2 ^ 59
def prefixEnd_2308392 : Nat := 4983230072969 + 3 ^ 40 * 2308392 * 2
def baseEnd_2308392 : Nat := 1185314634993637639383905

theorem tailTrace_2308392 : CollatzResearch.WordTrace tailWord_2308392 prefixEnd_2308392 1185314634993637639383905 := by
  unfold tailWord_2308392
  simp only [CollatzResearch.WordTrace]
  refine ⟨42096986526548750405751715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56129315368731667207668953 42096986526548750405751715)
  ·
    refine ⟨63145479789823125608627573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42096986526548750405751715 63145479789823125608627573)
    ·
      refine ⟨5919888730295918025808835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63145479789823125608627573 5919888730295918025808835)
      ·
        refine ⟨8879833095443877038713253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5919888730295918025808835 8879833095443877038713253)
        ·
          refine ⟨1664968705395726944758735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8879833095443877038713253 1664968705395726944758735)
          ·
            refine ⟨2497453058093590417138103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664968705395726944758735 2497453058093590417138103)
            ·
              refine ⟨3746179587140385625707155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497453058093590417138103 3746179587140385625707155)
              ·
                refine ⟨5619269380710578438560733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746179587140385625707155 5619269380710578438560733)
                ·
                  refine ⟨2107226017766466914460275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5619269380710578438560733 2107226017766466914460275)
                  ·
                    refine ⟨3160839026649700371690413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2107226017766466914460275 3160839026649700371690413)
                    ·
                      refine ⟨1185314634993637639383905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3160839026649700371690413 1185314634993637639383905)
                      ·
                        rfl

theorem cell23_2308392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_2308392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308392 prefixEnd_2308392 := by exact prefixLift 2308392
  have htrace : WordTrace (prefixWord ++ tailWord_2308392) baseStart_2308392 baseEnd_2308392 := by
    simpa [prefixWord, tailWord_2308392, baseEnd_2308392] using wordTrace_append hprefix tailTrace_2308392
  have hstable : (prefixWord ++ tailWord_2308392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308392).length < 2 ^ (prefixWord ++ tailWord_2308392).sum := by decide
  have hdescent : baseEnd_2308392 < baseStart_2308392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308408 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 2, 4]
def baseStart_2308408 : Nat := 118140960795 + 2308408 * 2 ^ 59
def prefixEnd_2308408 : Nat := 4983230072969 + 3 ^ 40 * 2308408 * 2
def baseEnd_2308408 : Nat := 395107616894703192261277

theorem tailTrace_2308408 : CollatzResearch.WordTrace tailWord_2308408 prefixEnd_2308408 395107616894703192261277 := by
  unfold tailWord_2308408
  simp only [CollatzResearch.WordTrace]
  refine ⟨42097278310519767772042939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56129704414026357029390585 42097278310519767772042939)
  ·
    refine ⟨63145917465779651658064409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42097278310519767772042939 63145917465779651658064409)
    ·
      refine ⟨47359438099334738743548307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63145917465779651658064409 47359438099334738743548307)
      ·
        refine ⟨71039157149002108115322461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47359438099334738743548307 71039157149002108115322461)
        ·
          refine ⟨26639683930875790543245923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71039157149002108115322461 26639683930875790543245923)
          ·
            refine ⟨39959525896313685814868885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26639683930875790543245923 39959525896313685814868885)
            ·
              refine ⟨1873102776389704022571979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39959525896313685814868885 1873102776389704022571979)
              ·
                refine ⟨2809654164584556033857969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873102776389704022571979 2809654164584556033857969)
                ·
                  refine ⟨2107240623438417025393477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2809654164584556033857969 2107240623438417025393477)
                  ·
                    refine ⟨395107616894703192261277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107240623438417025393477 395107616894703192261277)
                    ·
                      rfl

theorem cell23_2308408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_2308408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308408 prefixEnd_2308408 := by exact prefixLift 2308408
  have htrace : WordTrace (prefixWord ++ tailWord_2308408) baseStart_2308408 baseEnd_2308408 := by
    simpa [prefixWord, tailWord_2308408, baseEnd_2308408] using wordTrace_append hprefix tailTrace_2308408
  have hstable : (prefixWord ++ tailWord_2308408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308408).length < 2 ^ (prefixWord ++ tailWord_2308408).sum := by decide
  have hdescent : baseEnd_2308408 < baseStart_2308408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308431 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 3]
def baseStart_2308431 : Nat := 118140960795 + 2308431 * 2 ^ 59
def prefixEnd_2308431 : Nat := 4983230072969 + 3 ^ 40 * 2308431 * 2
def baseEnd_2308431 : Nat := 1185334660739162986796225

theorem tailTrace_2308431 : CollatzResearch.WordTrace tailWord_2308431 prefixEnd_2308431 1185334660739162986796225 := by
  unfold tailWord_2308431
  simp only [CollatzResearch.WordTrace]
  refine ⟨84195395499956210472173147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56130263666637473648115431 84195395499956210472173147)
  ·
    refine ⟨126293093249934315708259721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84195395499956210472173147 126293093249934315708259721)
    ·
      refine ⟨94719819937450736781194791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126293093249934315708259721 94719819937450736781194791)
      ·
        refine ⟨142079729906176105171792187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94719819937450736781194791 142079729906176105171792187)
        ·
          refine ⟨213119594859264157757688281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142079729906176105171792187 213119594859264157757688281)
          ·
            refine ⟨159839696144448118318266211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213119594859264157757688281 159839696144448118318266211)
            ·
              refine ⟨239759544216672177477399317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159839696144448118318266211 239759544216672177477399317)
              ·
                refine ⟨11238728635156508319253093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 239759544216672177477399317 11238728635156508319253093)
                ·
                  refine ⟨2107261619091845309859955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11238728635156508319253093 2107261619091845309859955)
                  ·
                    refine ⟨3160892428637767964789933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2107261619091845309859955 3160892428637767964789933)
                    ·
                      refine ⟨1185334660739162986796225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3160892428637767964789933 1185334660739162986796225)
                      ·
                        rfl

theorem cell23_2308431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 3].length) (baseStart_2308431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308431 prefixEnd_2308431 := by exact prefixLift 2308431
  have htrace : WordTrace (prefixWord ++ tailWord_2308431) baseStart_2308431 baseEnd_2308431 := by
    simpa [prefixWord, tailWord_2308431, baseEnd_2308431] using wordTrace_append hprefix tailTrace_2308431
  have hstable : (prefixWord ++ tailWord_2308431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308431).length < 2 ^ (prefixWord ++ tailWord_2308431).sum := by decide
  have hdescent : baseEnd_2308431 < baseStart_2308431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308464 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 1, 8]
def baseStart_2308464 : Nat := 118140960795 + 2308464 * 2 ^ 59
def prefixEnd_2308464 : Nat := 4983230072969 + 3 ^ 40 * 2308464 * 2
def baseEnd_2308464 : Nat := 395117201866920452561191

theorem tailTrace_2308464 : CollatzResearch.WordTrace tailWord_2308464 prefixEnd_2308464 395117201866920452561191 := by
  unfold tailWord_2308464
  simp only [CollatzResearch.WordTrace]
  refine ⟨42098299554418328554062223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56131066072557771405416297 42098299554418328554062223)
  ·
    refine ⟨63147449331627492831093335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42098299554418328554062223 63147449331627492831093335)
    ·
      refine ⟨94721173997441239246640003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63147449331627492831093335 94721173997441239246640003)
      ·
        refine ⟨142081760996161858869960005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94721173997441239246640003 142081760996161858869960005)
        ·
          refine ⟨26640330186780348538117501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142081760996161858869960005 26640330186780348538117501)
          ·
            refine ⟨9990123820042630701794063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26640330186780348538117501 9990123820042630701794063)
            ·
              refine ⟨14985185730063946052691095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9990123820042630701794063 14985185730063946052691095)
              ·
                refine ⟨22477778595095919079036643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14985185730063946052691095 22477778595095919079036643)
                ·
                  refine ⟨33716667892643878618554965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22477778595095919079036643 33716667892643878618554965)
                  ·
                    refine ⟨395117201866920452561191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33716667892643878618554965 395117201866920452561191)
                    ·
                      rfl

theorem cell23_2308464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_2308464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308464 prefixEnd_2308464 := by exact prefixLift 2308464
  have htrace : WordTrace (prefixWord ++ tailWord_2308464) baseStart_2308464 baseEnd_2308464 := by
    simpa [prefixWord, tailWord_2308464, baseEnd_2308464] using wordTrace_append hprefix tailTrace_2308464
  have hstable : (prefixWord ++ tailWord_2308464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308464).length < 2 ^ (prefixWord ++ tailWord_2308464).sum := by decide
  have hdescent : baseEnd_2308464 < baseStart_2308464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308488 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_2308488 : Nat := 118140960795 + 2308488 * 2 ^ 59
def prefixEnd_2308488 : Nat := 4983230072969 + 3 ^ 40 * 2308488 * 2
def baseEnd_2308488 : Nat := 1185363929136469263783463

theorem tailTrace_2308488 : CollatzResearch.WordTrace tailWord_2308488 prefixEnd_2308488 1185363929136469263783463 := by
  unfold tailWord_2308488
  simp only [CollatzResearch.WordTrace]
  refine ⟨42098737230374854603499059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56131649640499806137998745 42098737230374854603499059)
  ·
    refine ⟨63148105845562281905248589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42098737230374854603499059 63148105845562281905248589)
    ·
      refine ⟨23680539692085855714468221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63148105845562281905248589 23680539692085855714468221)
      ·
        refine ⟨8880202384532195892925583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23680539692085855714468221 8880202384532195892925583)
        ·
          refine ⟨13320303576798293839388375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8880202384532195892925583 13320303576798293839388375)
          ·
            refine ⟨19980455365197440759082563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13320303576798293839388375 19980455365197440759082563)
            ·
              refine ⟨29970683047796161138623845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19980455365197440759082563 29970683047796161138623845)
              ·
                refine ⟨5619503071461780213491971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29970683047796161138623845 5619503071461780213491971)
                ·
                  refine ⟨8429254607192670320237957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5619503071461780213491971 8429254607192670320237957)
                  ·
                    refine ⟨1580485238848625685044617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8429254607192670320237957 1580485238848625685044617)
                    ·
                      refine ⟨1185363929136469263783463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580485238848625685044617 1185363929136469263783463)
                      ·
                        rfl

theorem cell23_2308488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_2308488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308488 prefixEnd_2308488 := by exact prefixLift 2308488
  have htrace : WordTrace (prefixWord ++ tailWord_2308488) baseStart_2308488 baseEnd_2308488 := by
    simpa [prefixWord, tailWord_2308488, baseEnd_2308488] using wordTrace_append hprefix tailTrace_2308488
  have hstable : (prefixWord ++ tailWord_2308488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308488).length < 2 ^ (prefixWord ++ tailWord_2308488).sum := by decide
  have hdescent : baseEnd_2308488 < baseStart_2308488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308492 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 1, 3, 2]
def baseStart_2308492 : Nat := 118140960795 + 2308492 * 2 ^ 59
def prefixEnd_2308492 : Nat := 4983230072969 + 3 ^ 40 * 2308492 * 2
def baseEnd_2308492 : Nat := 1185365983059087248133445

theorem tailTrace_2308492 : CollatzResearch.WordTrace tailWord_2308492 prefixEnd_2308492 1185365983059087248133445 := by
  unfold tailWord_2308492
  simp only [CollatzResearch.WordTrace]
  refine ⟨42098810176367608945071865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56131746901823478593429153 42098810176367608945071865)
  ·
    refine ⟨31574107632275706708803899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42098810176367608945071865 31574107632275706708803899)
    ·
      refine ⟨47361161448413560063205849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31574107632275706708803899 47361161448413560063205849)
      ·
        refine ⟨35520871086310170047404387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47361161448413560063205849 35520871086310170047404387)
        ·
          refine ⟨53281306629465255071106581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35520871086310170047404387 53281306629465255071106581)
          ·
            refine ⟨2497561248256183831458121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53281306629465255071106581 2497561248256183831458121)
            ·
              refine ⟨1873170936192137873593591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497561248256183831458121 1873170936192137873593591)
              ·
                refine ⟨2809756404288206810390387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873170936192137873593591 2809756404288206810390387)
                ·
                  refine ⟨4214634606432310215585581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809756404288206810390387 4214634606432310215585581)
                  ·
                    refine ⟨1580487977412116330844593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4214634606432310215585581 1580487977412116330844593)
                    ·
                      refine ⟨1185365983059087248133445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580487977412116330844593 1185365983059087248133445)
                      ·
                        rfl

theorem cell23_2308492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_2308492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308492 prefixEnd_2308492 := by exact prefixLift 2308492
  have htrace : WordTrace (prefixWord ++ tailWord_2308492) baseStart_2308492 baseEnd_2308492 := by
    simpa [prefixWord, tailWord_2308492, baseEnd_2308492] using wordTrace_append hprefix tailTrace_2308492
  have hstable : (prefixWord ++ tailWord_2308492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308492).length < 2 ^ (prefixWord ++ tailWord_2308492).sum := by decide
  have hdescent : baseEnd_2308492 < baseStart_2308492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308511 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 7]
def baseStart_2308511 : Nat := 118140960795 + 2308511 * 2 ^ 59
def prefixEnd_2308511 : Nat := 4983230072969 + 3 ^ 40 * 2308511 * 2
def baseEnd_2308511 : Nat := 131708415465724741532873

theorem tailTrace_2308511 : CollatzResearch.WordTrace tailWord_2308511 prefixEnd_2308511 131708415465724741532873 := by
  unfold tailWord_2308511
  simp only [CollatzResearch.WordTrace]
  refine ⟨84198313339666384135085387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56132208893110922756723591 84198313339666384135085387)
  ·
    refine ⟨126297470009499576202628081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84198313339666384135085387 126297470009499576202628081)
    ·
      refine ⟨94723102507124682151971061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126297470009499576202628081 94723102507124682151971061)
      ·
        refine ⟨8880290860042938951747287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94723102507124682151971061 8880290860042938951747287)
        ·
          refine ⟨13320436290064408427620931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8880290860042938951747287 13320436290064408427620931)
          ·
            refine ⟨19980654435096612641431397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13320436290064408427620931 19980654435096612641431397)
            ·
              refine ⟨3746372706580614870268387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19980654435096612641431397 3746372706580614870268387)
              ·
                refine ⟨5619559059870922305402581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746372706580614870268387 5619559059870922305402581)
                ·
                  refine ⟨131708415465724741532873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5619559059870922305402581 131708415465724741532873)
                  ·
                    rfl

theorem cell23_2308511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 7].length) (baseStart_2308511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308511 prefixEnd_2308511 := by exact prefixLift 2308511
  have htrace : WordTrace (prefixWord ++ tailWord_2308511) baseStart_2308511 baseEnd_2308511 := by
    simpa [prefixWord, tailWord_2308511, baseEnd_2308511] using wordTrace_append hprefix tailTrace_2308511
  have hstable : (prefixWord ++ tailWord_2308511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308511).length < 2 ^ (prefixWord ++ tailWord_2308511).sum := by decide
  have hdescent : baseEnd_2308511 < baseStart_2308511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308541 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_2308541 : Nat := 118140960795 + 2308541 * 2 ^ 59
def prefixEnd_2308541 : Nat := 4983230072969 + 3 ^ 40 * 2308541 * 2
def baseEnd_2308541 : Nat := 395130381203719185473573

theorem tailTrace_2308541 : CollatzResearch.WordTrace tailWord_2308541 prefixEnd_2308541 395130381203719185473573 := by
  unfold tailWord_2308541
  simp only [CollatzResearch.WordTrace]
  refine ⟨84199407529557699258677477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56132938353038466172451651 84199407529557699258677477)
  ·
    refine ⟨15787388911792068611002027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84199407529557699258677477 15787388911792068611002027)
    ·
      refine ⟨23681083367688102916503041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15787388911792068611002027 23681083367688102916503041)
      ·
        refine ⟨17760812525766077187377281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23681083367688102916503041 17760812525766077187377281)
        ·
          refine ⟨13320609394324557890532961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17760812525766077187377281 13320609394324557890532961)
          ·
            refine ⟨9990457045743418417899721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13320609394324557890532961 9990457045743418417899721)
            ·
              refine ⟨7492842784307563813424791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9990457045743418417899721 7492842784307563813424791)
              ·
                refine ⟨11239264176461345720137187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7492842784307563813424791 11239264176461345720137187)
                ·
                  refine ⟨16858896264692018580205781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11239264176461345720137187 16858896264692018580205781)
                  ·
                    refine ⟨395130381203719185473573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16858896264692018580205781 395130381203719185473573)
                    ·
                      rfl

theorem cell23_2308541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_2308541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308541 prefixEnd_2308541 := by exact prefixLift 2308541
  have htrace : WordTrace (prefixWord ++ tailWord_2308541) baseStart_2308541 baseEnd_2308541 := by
    simpa [prefixWord, tailWord_2308541, baseEnd_2308541] using wordTrace_append hprefix tailTrace_2308541
  have hstable : (prefixWord ++ tailWord_2308541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308541).length < 2 ^ (prefixWord ++ tailWord_2308541).sum := by decide
  have hdescent : baseEnd_2308541 < baseStart_2308541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308562 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 7]
def baseStart_2308562 : Nat := 118140960795 + 2308562 * 2 ^ 59
def prefixEnd_2308562 : Nat := 4983230072969 + 3 ^ 40 * 2308562 * 2
def baseEnd_2308562 : Nat := 131711325189433552695347

theorem tailTrace_2308562 : CollatzResearch.WordTrace tailWord_2308562 prefixEnd_2308562 131711325189433552695347 := by
  unfold tailWord_2308562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21050043365620404961297985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56133448974987746563461293 21050043365620404961297985)
  ·
    refine ⟨15787532524215303720973489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21050043365620404961297985 15787532524215303720973489)
    ·
      refine ⟨11840649393161477790730117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15787532524215303720973489 11840649393161477790730117)
      ·
        refine ⟨2220121761217777085761897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11840649393161477790730117 2220121761217777085761897)
        ·
          refine ⟨1665091320913332814321423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2220121761217777085761897 1665091320913332814321423)
          ·
            refine ⟨2497636981369999221482135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665091320913332814321423 2497636981369999221482135)
            ·
              refine ⟨3746455472054998832223203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497636981369999221482135 3746455472054998832223203)
              ·
                refine ⟨5619683208082498248334805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746455472054998832223203 5619683208082498248334805)
                ·
                  refine ⟨131711325189433552695347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5619683208082498248334805 131711325189433552695347)
                  ·
                    rfl

theorem cell23_2308562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_2308562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308562 prefixEnd_2308562 := by exact prefixLift 2308562
  have htrace : WordTrace (prefixWord ++ tailWord_2308562) baseStart_2308562 baseEnd_2308562 := by
    simpa [prefixWord, tailWord_2308562, baseEnd_2308562] using wordTrace_append hprefix tailTrace_2308562
  have hstable : (prefixWord ++ tailWord_2308562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308562).length < 2 ^ (prefixWord ++ tailWord_2308562).sum := by decide
  have hdescent : baseEnd_2308562 < baseStart_2308562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308605 : List Nat := [1, 4, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_2308605 : Nat := 118140960795 + 2308605 * 2 ^ 59
def prefixEnd_2308605 : Nat := 4983230072969 + 3 ^ 40 * 2308605 * 2
def baseEnd_2308605 : Nat := 395141335457681768673475

theorem tailTrace_2308605 : CollatzResearch.WordTrace tailWord_2308605 prefixEnd_2308605 395141335457681768673475 := by
  unfold tailWord_2308605
  simp only [CollatzResearch.WordTrace]
  refine ⟨84201741801325838189007269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56134494534217225459338179 84201741801325838189007269)
  ·
    refine ⟨15787826587748594660438863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84201741801325838189007269 15787826587748594660438863)
    ·
      refine ⟨23681739881622891990658295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15787826587748594660438863 23681739881622891990658295)
      ·
        refine ⟨35522609822434337985987443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23681739881622891990658295 35522609822434337985987443)
        ·
          refine ⟨53283914733651506978981165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35522609822434337985987443 53283914733651506978981165)
          ·
            refine ⟨19981468025119315117117937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53283914733651506978981165 19981468025119315117117937)
            ·
              refine ⟨14986101018839486337838453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19981468025119315117117937 14986101018839486337838453)
              ·
                refine ⟨1404946970516201844172355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14986101018839486337838453 1404946970516201844172355)
                ·
                  refine ⟨2107420455774302766258533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404946970516201844172355 2107420455774302766258533)
                  ·
                    refine ⟨395141335457681768673475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107420455774302766258533 395141335457681768673475)
                    ·
                      rfl

theorem cell23_2308605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_2308605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308605 prefixEnd_2308605 := by exact prefixLift 2308605
  have htrace : WordTrace (prefixWord ++ tailWord_2308605) baseStart_2308605 baseEnd_2308605 := by
    simpa [prefixWord, tailWord_2308605, baseEnd_2308605] using wordTrace_append hprefix tailTrace_2308605
  have hstable : (prefixWord ++ tailWord_2308605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308605).length < 2 ^ (prefixWord ++ tailWord_2308605).sum := by decide
  have hdescent : baseEnd_2308605 < baseStart_2308605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308618 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 6]
def baseStart_2308618 : Nat := 118140960795 + 2308618 * 2 ^ 59
def prefixEnd_2308618 : Nat := 4983230072969 + 3 ^ 40 * 2308618 * 2
def baseEnd_2308618 : Nat := 131714520180172639461985

theorem tailTrace_2308618 : CollatzResearch.WordTrace tailWord_2308618 prefixEnd_2308618 131714520180172639461985 := by
  unfold tailWord_2308618
  simp only [CollatzResearch.WordTrace]
  refine ⟨21050553987569685352307627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56134810633519160939487005 21050553987569685352307627)
  ·
    refine ⟨31575830981354528028461441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21050553987569685352307627 31575830981354528028461441)
    ·
      refine ⟨23681873236015896021346081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31575830981354528028461441 23681873236015896021346081)
      ·
        refine ⟨17761404927011922016009561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23681873236015896021346081 17761404927011922016009561)
        ·
          refine ⟨13321053695258941512007171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17761404927011922016009561 13321053695258941512007171)
          ·
            refine ⟨19981580542888412268010757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13321053695258941512007171 19981580542888412268010757)
            ·
              refine ⟨3746546351791577300252017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19981580542888412268010757 3746546351791577300252017)
              ·
                refine ⟨2809909763843682975189013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3746546351791577300252017 2809909763843682975189013)
                ·
                  refine ⟨131714520180172639461985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2809909763843682975189013 131714520180172639461985)
                  ·
                    rfl

theorem cell23_2308618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_2308618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308618 prefixEnd_2308618 := by exact prefixLift 2308618
  have htrace : WordTrace (prefixWord ++ tailWord_2308618) baseStart_2308618 baseEnd_2308618 := by
    simpa [prefixWord, tailWord_2308618, baseEnd_2308618] using wordTrace_append hprefix tailTrace_2308618
  have hstable : (prefixWord ++ tailWord_2308618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308618).length < 2 ^ (prefixWord ++ tailWord_2308618).sum := by decide
  have hdescent : baseEnd_2308618 < baseStart_2308618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308622 : List Nat := [4, 1, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_2308622 : Nat := 118140960795 + 2308622 * 2 ^ 59
def prefixEnd_2308622 : Nat := 4983230072969 + 3 ^ 40 * 2308622 * 2
def baseEnd_2308622 : Nat := 395144245181390579835949

theorem tailTrace_2308622 : CollatzResearch.WordTrace tailWord_2308622 prefixEnd_2308622 395144245181390579835949 := by
  unfold tailWord_2308622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525295230283031261547015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56134907894842833394917413 10525295230283031261547015)
  ·
    refine ⟨15787942845424546892320523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10525295230283031261547015 15787942845424546892320523)
    ·
      refine ⟨23681914268136820338480785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15787942845424546892320523 23681914268136820338480785)
      ·
        refine ⟨17761435701102615253860589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23681914268136820338480785 17761435701102615253860589)
        ·
          refine ⟨6660538387913480720197721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17761435701102615253860589 6660538387913480720197721)
          ·
            refine ⟨4995403790935110540148291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6660538387913480720197721 4995403790935110540148291)
            ·
              refine ⟨7493105686402665810222437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4995403790935110540148291 7493105686402665810222437)
              ·
                refine ⟨1404957316200499839416707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7493105686402665810222437 1404957316200499839416707)
                ·
                  refine ⟨2107435974300749759125061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404957316200499839416707 2107435974300749759125061)
                  ·
                    refine ⟨395144245181390579835949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107435974300749759125061 395144245181390579835949)
                    ·
                      rfl

theorem cell23_2308622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_2308622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308622 prefixEnd_2308622 := by exact prefixLift 2308622
  have htrace : WordTrace (prefixWord ++ tailWord_2308622) baseStart_2308622 baseEnd_2308622 := by
    simpa [prefixWord, tailWord_2308622, baseEnd_2308622] using wordTrace_append hprefix tailTrace_2308622
  have hstable : (prefixWord ++ tailWord_2308622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308622).length < 2 ^ (prefixWord ++ tailWord_2308622).sum := by decide
  have hdescent : baseEnd_2308622 < baseStart_2308622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308641 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2308641 : Nat := 118140960795 + 2308641 * 2 ^ 59
def prefixEnd_2308641 : Nat := 4983230072969 + 3 ^ 40 * 2308641 * 2
def baseEnd_2308641 : Nat := 1185442491676607165170259

theorem tailTrace_2308641 : CollatzResearch.WordTrace tailWord_2308641 prefixEnd_2308641 1185442491676607165170259 := by
  unfold tailWord_2308641
  simp only [CollatzResearch.WordTrace]
  refine ⟨84203054829195416337317777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56135369886130277558211851 84203054829195416337317777)
  ·
    refine ⟨63152291121896562252988333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84203054829195416337317777 63152291121896562252988333)
    ·
      refine ⟨23682109170711210844870625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63152291121896562252988333 23682109170711210844870625)
      ·
        refine ⟨17761581878033408133652969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23682109170711210844870625 17761581878033408133652969)
        ·
          refine ⟨13321186408525056100239727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17761581878033408133652969 13321186408525056100239727)
          ·
            refine ⟨19981779612787584150359591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13321186408525056100239727 19981779612787584150359591)
            ·
              refine ⟨29972669419181376225539387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19981779612787584150359591 29972669419181376225539387)
              ·
                refine ⟨44959004128772064338309081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29972669419181376225539387 44959004128772064338309081)
                ·
                  refine ⟨33719253096579048253731811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44959004128772064338309081 33719253096579048253731811)
                  ·
                    refine ⟨50578879644868572380597717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33719253096579048253731811 50578879644868572380597717)
                    ·
                      refine ⟨1185442491676607165170259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50578879644868572380597717 1185442491676607165170259)
                      ·
                        rfl

theorem cell23_2308641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2308641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308641 prefixEnd_2308641 := by exact prefixLift 2308641
  have htrace : WordTrace (prefixWord ++ tailWord_2308641) baseStart_2308641 baseEnd_2308641 := by
    simpa [prefixWord, tailWord_2308641, baseEnd_2308641] using wordTrace_append hprefix tailTrace_2308641
  have hstable : (prefixWord ++ tailWord_2308641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308641).length < 2 ^ (prefixWord ++ tailWord_2308641).sum := by decide
  have hdescent : baseEnd_2308641 < baseStart_2308641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308681 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_2308681 : Nat := 118140960795 + 2308681 * 2 ^ 59
def prefixEnd_2308681 : Nat := 4983230072969 + 3 ^ 40 * 2308681 * 2
def baseEnd_2308681 : Nat := 1185463030902787008670075

theorem tailTrace_2308681 : CollatzResearch.WordTrace tailWord_2308681 prefixEnd_2308681 1185463030902787008670075 := by
  unfold tailWord_2308681
  simp only [CollatzResearch.WordTrace]
  refine ⟨84204513749050503168773897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56136342499367002112515931 84204513749050503168773897)
  ·
    refine ⟨63153385311787877376580423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84204513749050503168773897 63153385311787877376580423)
    ·
      refine ⟨94730077967681816064870635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63153385311787877376580423 94730077967681816064870635)
      ·
        refine ⟨142095116951522724097305953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94730077967681816064870635 142095116951522724097305953)
        ·
          refine ⟨106571337713642043072979465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142095116951522724097305953 106571337713642043072979465)
          ·
            refine ⟨79928503285231532304734599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106571337713642043072979465 79928503285231532304734599)
            ·
              refine ⟨119892754927847298457101899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79928503285231532304734599 119892754927847298457101899)
              ·
                refine ⟨179839132391770947685652849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119892754927847298457101899 179839132391770947685652849)
                ·
                  refine ⟨134879349293828210764239637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179839132391770947685652849 134879349293828210764239637)
                  ·
                    refine ⟨6322469498148197379573733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 134879349293828210764239637 6322469498148197379573733)
                    ·
                      refine ⟨1185463030902787008670075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6322469498148197379573733 1185463030902787008670075)
                      ·
                        rfl

theorem cell23_2308681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_2308681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308681 prefixEnd_2308681 := by exact prefixLift 2308681
  have htrace : WordTrace (prefixWord ++ tailWord_2308681) baseStart_2308681 baseEnd_2308681 := by
    simpa [prefixWord, tailWord_2308681, baseEnd_2308681] using wordTrace_append hprefix tailTrace_2308681
  have hstable : (prefixWord ++ tailWord_2308681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308681).length < 2 ^ (prefixWord ++ tailWord_2308681).sum := by decide
  have hdescent : baseEnd_2308681 < baseStart_2308681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308688 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 3]
def baseStart_2308688 : Nat := 118140960795 + 2308688 * 2 ^ 59
def prefixEnd_2308688 : Nat := 4983230072969 + 3 ^ 40 * 2308688 * 2
def baseEnd_2308688 : Nat := 1185466625267368481282543

theorem tailTrace_2308688 : CollatzResearch.WordTrace tailWord_2308688 prefixEnd_2308688 1185466625267368481282543 := by
  unfold tailWord_2308688
  simp only [CollatzResearch.WordTrace]
  refine ⟨42102384530012571682139359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56136512706683428909519145 42102384530012571682139359)
  ·
    refine ⟨63153576795018857523209039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42102384530012571682139359 63153576795018857523209039)
    ·
      refine ⟨94730365192528286284813559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63153576795018857523209039 94730365192528286284813559)
      ·
        refine ⟨142095547788792429427220339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94730365192528286284813559 142095547788792429427220339)
        ·
          refine ⟨213143321683188644140830509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142095547788792429427220339 213143321683188644140830509)
          ·
            refine ⟨79928745631195741552811441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213143321683188644140830509 79928745631195741552811441)
            ·
              refine ⟨59946559223396806164608581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79928745631195741552811441 59946559223396806164608581)
              ·
                refine ⟨11239979854386901155864109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59946559223396806164608581 11239979854386901155864109)
                ·
                  refine ⟨4214992445395087933449041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11239979854386901155864109 4214992445395087933449041)
                  ·
                    refine ⟨3161244334046315950086781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4214992445395087933449041 3161244334046315950086781)
                    ·
                      refine ⟨1185466625267368481282543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3161244334046315950086781 1185466625267368481282543)
                      ·
                        rfl

theorem cell23_2308688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_2308688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308688 prefixEnd_2308688 := by exact prefixLift 2308688
  have htrace : WordTrace (prefixWord ++ tailWord_2308688) baseStart_2308688 baseEnd_2308688 := by
    simpa [prefixWord, tailWord_2308688, baseEnd_2308688] using wordTrace_append hprefix tailTrace_2308688
  have hstable : (prefixWord ++ tailWord_2308688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308688).length < 2 ^ (prefixWord ++ tailWord_2308688).sum := by decide
  have hdescent : baseEnd_2308688 < baseStart_2308688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308705 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_2308705 : Nat := 118140960795 + 2308705 * 2 ^ 59
def prefixEnd_2308705 : Nat := 4983230072969 + 3 ^ 40 * 2308705 * 2
def baseEnd_2308705 : Nat := 1185475354438494914769965

theorem tailTrace_2308705 : CollatzResearch.WordTrace tailWord_2308705 prefixEnd_2308705 1185475354438494914769965 := by
  unfold tailWord_2308705
  simp only [CollatzResearch.WordTrace]
  refine ⟨84205389100963555267647569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56136926067309036845098379 84205389100963555267647569)
  ·
    refine ⟨63154041825722666450735677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84205389100963555267647569 63154041825722666450735677)
    ·
      refine ⟨23682765684645999919025879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63154041825722666450735677 23682765684645999919025879)
      ·
        refine ⟨35524148526968999878538819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23682765684645999919025879 35524148526968999878538819)
        ·
          refine ⟨53286222790453499817808229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35524148526968999878538819 53286222790453499817808229)
          ·
            refine ⟨9991166773210031215839043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53286222790453499817808229 9991166773210031215839043)
            ·
              refine ⟨14986750159815046823758565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9991166773210031215839043 14986750159815046823758565)
              ·
                refine ⟨2810015654965321279454731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14986750159815046823758565 2810015654965321279454731)
                ·
                  refine ⟨4215023482447981919182097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810015654965321279454731 4215023482447981919182097)
                  ·
                    refine ⟨3161267611835986439386573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4215023482447981919182097 3161267611835986439386573)
                    ·
                      refine ⟨1185475354438494914769965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3161267611835986439386573 1185475354438494914769965)
                      ·
                        rfl

theorem cell23_2308705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_2308705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308705 prefixEnd_2308705 := by exact prefixLift 2308705
  have htrace : WordTrace (prefixWord ++ tailWord_2308705) baseStart_2308705 baseEnd_2308705 := by
    simpa [prefixWord, tailWord_2308705, baseEnd_2308705] using wordTrace_append hprefix tailTrace_2308705
  have hstable : (prefixWord ++ tailWord_2308705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308705).length < 2 ^ (prefixWord ++ tailWord_2308705).sum := by decide
  have hdescent : baseEnd_2308705 < baseStart_2308705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308719 : List Nat := [1, 1, 2, 1, 3, 2, 5, 3, 1, 2, 2]
def baseStart_2308719 : Nat := 118140960795 + 2308719 * 2 ^ 59
def prefixEnd_2308719 : Nat := 4983230072969 + 3 ^ 40 * 2308719 * 2
def baseEnd_2308719 : Nat := 1185482543167657859994901

theorem tailTrace_2308719 : CollatzResearch.WordTrace tailWord_2308719 prefixEnd_2308719 1185482543167657859994901 := by
  unfold tailWord_2308719
  simp only [CollatzResearch.WordTrace]
  refine ⟨84205899722912835658657211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56137266481941890439104807 84205899722912835658657211)
  ·
    refine ⟨126308849584369253487985817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84205899722912835658657211 126308849584369253487985817)
    ·
      refine ⟨94731637188276940115989363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126308849584369253487985817 94731637188276940115989363)
      ·
        refine ⟨142097455782415410173984045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94731637188276940115989363 142097455782415410173984045)
        ·
          refine ⟨53286545918405778815244017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142097455782415410173984045 53286545918405778815244017)
          ·
            refine ⟨39964909438804334111433013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53286545918405778815244017 39964909438804334111433013)
            ·
              refine ⟨3746710259887906322946845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39964909438804334111433013 3746710259887906322946845)
              ·
                refine ⟨1405016347457964871105067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3746710259887906322946845 1405016347457964871105067)
                ·
                  refine ⟨2107524521186947306657601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405016347457964871105067 2107524521186947306657601)
                  ·
                    refine ⟨1580643390890210479993201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2107524521186947306657601 1580643390890210479993201)
                    ·
                      refine ⟨1185482543167657859994901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580643390890210479993201 1185482543167657859994901)
                      ·
                        rfl

theorem cell23_2308719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 2, 2].length) (baseStart_2308719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308719 prefixEnd_2308719 := by exact prefixLift 2308719
  have htrace : WordTrace (prefixWord ++ tailWord_2308719) baseStart_2308719 baseEnd_2308719 := by
    simpa [prefixWord, tailWord_2308719, baseEnd_2308719] using wordTrace_append hprefix tailTrace_2308719
  have hstable : (prefixWord ++ tailWord_2308719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308719).length < 2 ^ (prefixWord ++ tailWord_2308719).sum := by decide
  have hdescent : baseEnd_2308719 < baseStart_2308719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308721 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 3, 9]
def baseStart_2308721 : Nat := 118140960795 + 2308721 * 2 ^ 59
def prefixEnd_2308721 : Nat := 4983230072969 + 3 ^ 40 * 2308721 * 2
def baseEnd_2308721 : Nat := 395161190042988950723297

theorem tailTrace_2308721 : CollatzResearch.WordTrace tailWord_2308721 prefixEnd_2308721 395161190042988950723297 := by
  unfold tailWord_2308721
  simp only [CollatzResearch.WordTrace]
  refine ⟨84205972668905590000230017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56137315112603726666820011 84205972668905590000230017)
  ·
    refine ⟨63154479501679192500172513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84205972668905590000230017 63154479501679192500172513)
    ·
      refine ⟨47365859626259394375129385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63154479501679192500172513 47365859626259394375129385)
      ·
        refine ⟨35524394719694545781347039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47365859626259394375129385 35524394719694545781347039)
        ·
          refine ⟨53286592079541818672020559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35524394719694545781347039 53286592079541818672020559)
          ·
            refine ⟨79929888119312728008030839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53286592079541818672020559 79929888119312728008030839)
            ·
              refine ⟨119894832178969092012046259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79929888119312728008030839 119894832178969092012046259)
              ·
                refine ⟨179842248268453638018069389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119894832178969092012046259 179842248268453638018069389)
                ·
                  refine ⟨67440843100670114256776021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179842248268453638018069389 67440843100670114256776021)
                  ·
                    refine ⟨395161190042988950723297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 67440843100670114256776021 395161190042988950723297)
                    ·
                      rfl

theorem cell23_2308721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_2308721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308721 prefixEnd_2308721 := by exact prefixLift 2308721
  have htrace : WordTrace (prefixWord ++ tailWord_2308721) baseStart_2308721 baseEnd_2308721 := by
    simpa [prefixWord, tailWord_2308721, baseEnd_2308721] using wordTrace_append hprefix tailTrace_2308721
  have hstable : (prefixWord ++ tailWord_2308721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308721).length < 2 ^ (prefixWord ++ tailWord_2308721).sum := by decide
  have hdescent : baseEnd_2308721 < baseStart_2308721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308725 : List Nat := [1, 3, 4, 2, 2, 2, 9]
def baseStart_2308725 : Nat := 118140960795 + 2308725 * 2 ^ 59
def prefixEnd_2308725 : Nat := 4983230072969 + 3 ^ 40 * 2308725 * 2
def baseEnd_2308725 : Nat := 14635624988291170821233

theorem tailTrace_2308725 : CollatzResearch.WordTrace tailWord_2308725 prefixEnd_2308725 14635624988291170821233 := by
  unfold tailWord_2308725
  simp only [CollatzResearch.WordTrace]
  refine ⟨84206118560891098683375629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56137412373927399122250419 84206118560891098683375629)
  ·
    refine ⟨31577294460334162006265861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84206118560891098683375629 31577294460334162006265861)
    ·
      refine ⟨5920742711312655376174849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31577294460334162006265861 5920742711312655376174849)
      ·
        refine ⟨4440557033484491532131137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5920742711312655376174849 4440557033484491532131137)
        ·
          refine ⟨3330417775113368649098353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4440557033484491532131137 3330417775113368649098353)
          ·
            refine ⟨2497813331335026486823765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3330417775113368649098353 2497813331335026486823765)
            ·
              refine ⟨14635624988291170821233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2497813331335026486823765 14635624988291170821233)
              ·
                rfl

theorem cell23_2308725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 9].length) (baseStart_2308725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308725 prefixEnd_2308725 := by exact prefixLift 2308725
  have htrace : WordTrace (prefixWord ++ tailWord_2308725) baseStart_2308725 baseEnd_2308725 := by
    simpa [prefixWord, tailWord_2308725, baseEnd_2308725] using wordTrace_append hprefix tailTrace_2308725
  have hstable : (prefixWord ++ tailWord_2308725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308725).length < 2 ^ (prefixWord ++ tailWord_2308725).sum := by decide
  have hdescent : baseEnd_2308725 < baseStart_2308725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308736 : List Nat := [2, 1, 1, 2, 1, 6, 3, 2, 1, 2, 2]
def baseStart_2308736 : Nat := 118140960795 + 2308736 * 2 ^ 59
def prefixEnd_2308736 : Nat := 4983230072969 + 3 ^ 40 * 2308736 * 2
def baseEnd_2308736 : Nat := 1185491272338784293482323

theorem tailTrace_2308736 : CollatzResearch.WordTrace tailWord_2308736 prefixEnd_2308736 1185491272338784293482323 := by
  unfold tailWord_2308736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42103259881925623781013031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56137679842567498374684041 42103259881925623781013031)
  ·
    refine ⟨63154889822888435671519547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42103259881925623781013031 63154889822888435671519547)
    ·
      refine ⟨94732334734332653507279321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63154889822888435671519547 94732334734332653507279321)
      ·
        refine ⟨71049251050749490130459491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94732334734332653507279321 71049251050749490130459491)
        ·
          refine ⟨106573876576124235195689237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71049251050749490130459491 106573876576124235195689237)
          ·
            refine ⟨4995650464505823524797933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106573876576124235195689237 4995650464505823524797933)
            ·
              refine ⟨1873368924189683821799225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4995650464505823524797933 1873368924189683821799225)
              ·
                refine ⟨1405026693142262866349419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873368924189683821799225 1405026693142262866349419)
                ·
                  refine ⟨2107540039713394299524129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405026693142262866349419 2107540039713394299524129)
                  ·
                    refine ⟨1580655029785045724643097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2107540039713394299524129 1580655029785045724643097)
                    ·
                      refine ⟨1185491272338784293482323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580655029785045724643097 1185491272338784293482323)
                      ·
                        rfl

theorem cell23_2308736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_2308736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308736 prefixEnd_2308736 := by exact prefixLift 2308736
  have htrace : WordTrace (prefixWord ++ tailWord_2308736) baseStart_2308736 baseEnd_2308736 := by
    simpa [prefixWord, tailWord_2308736, baseEnd_2308736] using wordTrace_append hprefix tailTrace_2308736
  have hstable : (prefixWord ++ tailWord_2308736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308736).length < 2 ^ (prefixWord ++ tailWord_2308736).sum := by decide
  have hdescent : baseEnd_2308736 < baseStart_2308736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308745 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 3, 3, 2]
def baseStart_2308745 : Nat := 118140960795 + 2308745 * 2 ^ 59
def prefixEnd_2308745 : Nat := 4983230072969 + 3 ^ 40 * 2308745 * 2
def baseEnd_2308745 : Nat := 1185495893664674758269781

theorem tailTrace_2308745 : CollatzResearch.WordTrace tailWord_2308745 prefixEnd_2308745 1185495893664674758269781 := by
  unfold tailWord_2308745
  simp only [CollatzResearch.WordTrace]
  refine ⟨84206848020818642099103689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56137898680545761399402459 84206848020818642099103689)
  ·
    refine ⟨63155136015613981574327767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84206848020818642099103689 63155136015613981574327767)
    ·
      refine ⟨94732704023420972361491651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63155136015613981574327767 94732704023420972361491651)
      ·
        refine ⟨142099056035131458542237477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94732704023420972361491651 142099056035131458542237477)
        ·
          refine ⟨26643573006587148476669527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142099056035131458542237477 26643573006587148476669527)
          ·
            refine ⟨39965359509880722715004291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26643573006587148476669527 39965359509880722715004291)
            ·
              refine ⟨59948039264821084072506437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39965359509880722715004291 59948039264821084072506437)
              ·
                refine ⟨11240257362153953263594957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59948039264821084072506437 11240257362153953263594957)
                ·
                  refine ⟨4215096510807732473848109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11240257362153953263594957 4215096510807732473848109)
                  ·
                    refine ⟨1580661191552899677693041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4215096510807732473848109 1580661191552899677693041)
                    ·
                      refine ⟨1185495893664674758269781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580661191552899677693041 1185495893664674758269781)
                      ·
                        rfl

theorem cell23_2308745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 3, 2].length) (baseStart_2308745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308745 prefixEnd_2308745 := by exact prefixLift 2308745
  have htrace : WordTrace (prefixWord ++ tailWord_2308745) baseStart_2308745 baseEnd_2308745 := by
    simpa [prefixWord, tailWord_2308745, baseEnd_2308745] using wordTrace_append hprefix tailTrace_2308745
  have hstable : (prefixWord ++ tailWord_2308745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308745).length < 2 ^ (prefixWord ++ tailWord_2308745).sum := by decide
  have hdescent : baseEnd_2308745 < baseStart_2308745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308746 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_2308746 : Nat := 118140960795 + 2308746 * 2 ^ 59
def prefixEnd_2308746 : Nat := 4983230072969 + 3 ^ 40 * 2308746 * 2
def baseEnd_2308746 : Nat := 395165469048443084785759

theorem tailTrace_2308746 : CollatzResearch.WordTrace tailWord_2308746 prefixEnd_2308746 395165469048443084785759 := by
  unfold tailWord_2308746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21051721123453754817472523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56137922995876679513260061 21051721123453754817472523)
  ·
    refine ⟨31577581685180632226208785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21051721123453754817472523 31577581685180632226208785)
    ·
      refine ⟨23683186263885474169656589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31577581685180632226208785 23683186263885474169656589)
      ·
        refine ⟨8881194848957052813621221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23683186263885474169656589 8881194848957052813621221)
        ·
          refine ⟨1665224034179447402553979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8881194848957052813621221 1665224034179447402553979)
          ·
            refine ⟨2497836051269171103830969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665224034179447402553979 2497836051269171103830969)
            ·
              refine ⟨1873377038451878327873227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497836051269171103830969 1873377038451878327873227)
              ·
                refine ⟨2810065557677817491809841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873377038451878327873227 2810065557677817491809841)
                ·
                  refine ⟨2107549168258363118857381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2810065557677817491809841 2107549168258363118857381)
                  ·
                    refine ⟨395165469048443084785759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107549168258363118857381 395165469048443084785759)
                    ·
                      rfl

theorem cell23_2308746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_2308746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308746 prefixEnd_2308746 := by exact prefixLift 2308746
  have htrace : WordTrace (prefixWord ++ tailWord_2308746) baseStart_2308746 baseEnd_2308746 := by
    simpa [prefixWord, tailWord_2308746, baseEnd_2308746] using wordTrace_append hprefix tailTrace_2308746
  have hstable : (prefixWord ++ tailWord_2308746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308746).length < 2 ^ (prefixWord ++ tailWord_2308746).sum := by decide
  have hdescent : baseEnd_2308746 < baseStart_2308746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308845 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2308845 : Nat := 118140960795 + 2308845 * 2 ^ 59
def prefixEnd_2308845 : Nat := 4983230072969 + 3 ^ 40 * 2308845 * 2
def baseEnd_2308845 : Nat := 395182413910041455673107

theorem tailTrace_2308845 : CollatzResearch.WordTrace tailWord_2308845 prefixEnd_2308845 395182413910041455673107 := by
  unfold tailWord_2308845
  simp only [CollatzResearch.WordTrace]
  refine ⟨84210495320456359177743989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56140330213637572785162659 84210495320456359177743989)
  ·
    refine ⟨7894733936292783672913499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84210495320456359177743989 7894733936292783672913499)
    ·
      refine ⟨11842100904439175509370249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7894733936292783672913499 11842100904439175509370249)
      ·
        refine ⟨8881575678329381632027687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11842100904439175509370249 8881575678329381632027687)
        ·
          refine ⟨13322363517494072448041531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8881575678329381632027687 13322363517494072448041531)
          ·
            refine ⟨19983545276241108672062297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13322363517494072448041531 19983545276241108672062297)
            ·
              refine ⟨14987658957180831504046723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19983545276241108672062297 14987658957180831504046723)
              ·
                refine ⟨22481488435771247256070085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14987658957180831504046723 22481488435771247256070085)
                ·
                  refine ⟨4215279081707108860513141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22481488435771247256070085 4215279081707108860513141)
                  ·
                    refine ⟨395182413910041455673107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4215279081707108860513141 395182413910041455673107)
                    ·
                      rfl

theorem cell23_2308845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2308845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308845 prefixEnd_2308845 := by exact prefixLift 2308845
  have htrace : WordTrace (prefixWord ++ tailWord_2308845) baseStart_2308845 baseEnd_2308845 := by
    simpa [prefixWord, tailWord_2308845, baseEnd_2308845] using wordTrace_append hprefix tailTrace_2308845
  have hstable : (prefixWord ++ tailWord_2308845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308845).length < 2 ^ (prefixWord ++ tailWord_2308845).sum := by decide
  have hdescent : baseEnd_2308845 < baseStart_2308845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308885 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_2308885 : Nat := 118140960795 + 2308885 * 2 ^ 59
def prefixEnd_2308885 : Nat := 4983230072969 + 3 ^ 40 * 2308885 * 2
def baseEnd_2308885 : Nat := 1185567780956304210519137

theorem tailTrace_2308885 : CollatzResearch.WordTrace tailWord_2308885 prefixEnd_2308885 1185567780956304210519137 := by
  unfold tailWord_2308885
  simp only [CollatzResearch.WordTrace]
  refine ⟨84211954240311446009200109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56141302826874297339466739 84211954240311446009200109)
  ·
    refine ⟨31579482840116792253450041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84211954240311446009200109 31579482840116792253450041)
    ·
      refine ⟨23684612130087594190087531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31579482840116792253450041 23684612130087594190087531)
      ·
        refine ⟨35526918195131391285131297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23684612130087594190087531 35526918195131391285131297)
        ·
          refine ⟨26645188646348543463848473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35526918195131391285131297 26645188646348543463848473)
          ·
            refine ⟨19983891484761407597886355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26645188646348543463848473 19983891484761407597886355)
            ·
              refine ⟨29975837227142111396829533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19983891484761407597886355 29975837227142111396829533)
              ·
                refine ⟨11240938960178291773811075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29975837227142111396829533 11240938960178291773811075)
                ·
                  refine ⟨16861408440267437660716613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11240938960178291773811075 16861408440267437660716613)
                  ·
                    refine ⟨3161514082550144561384365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16861408440267437660716613 3161514082550144561384365)
                    ·
                      refine ⟨1185567780956304210519137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3161514082550144561384365 1185567780956304210519137)
                      ·
                        rfl

theorem cell23_2308885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_2308885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308885 prefixEnd_2308885 := by exact prefixLift 2308885
  have htrace : WordTrace (prefixWord ++ tailWord_2308885) baseStart_2308885 baseEnd_2308885 := by
    simpa [prefixWord, tailWord_2308885, baseEnd_2308885] using wordTrace_append hprefix tailTrace_2308885
  have hstable : (prefixWord ++ tailWord_2308885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308885).length < 2 ^ (prefixWord ++ tailWord_2308885).sum := by decide
  have hdescent : baseEnd_2308885 < baseStart_2308885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308922 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 6]
def baseStart_2308922 : Nat := 118140960795 + 2308922 * 2 ^ 59
def prefixEnd_2308922 : Nat := 4983230072969 + 3 ^ 40 * 2308922 * 2
def baseEnd_2308922 : Nat := 131731864415613396195163

theorem tailTrace_2308922 : CollatzResearch.WordTrace tailWord_2308922 prefixEnd_2308922 131731864415613396195163 := by
  unfold tailWord_2308922
  simp only [CollatzResearch.WordTrace]
  refine ⟨21053325935294350332074255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56142202494118267552198013 21053325935294350332074255)
  ·
    refine ⟨31579988902941525498111383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21053325935294350332074255 31579988902941525498111383)
    ·
      refine ⟨47369983354412288247167075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31579988902941525498111383 47369983354412288247167075)
      ·
        refine ⟨71054975031618432370750613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47369983354412288247167075 71054975031618432370750613)
        ·
          refine ⟨3330701954607114017378935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71054975031618432370750613 3330701954607114017378935)
          ·
            refine ⟨4996052931910671026068403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330701954607114017378935 4996052931910671026068403)
            ·
              refine ⟨7494079397866006539102605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4996052931910671026068403 7494079397866006539102605)
              ·
                refine ⟨2810279774199752452163477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7494079397866006539102605 2810279774199752452163477)
                ·
                  refine ⟨131731864415613396195163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2810279774199752452163477 131731864415613396195163)
                  ·
                    rfl

theorem cell23_2308922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_2308922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308922 prefixEnd_2308922 := by exact prefixLift 2308922
  have htrace : WordTrace (prefixWord ++ tailWord_2308922) baseStart_2308922 baseEnd_2308922 := by
    simpa [prefixWord, tailWord_2308922, baseEnd_2308922] using wordTrace_append hprefix tailTrace_2308922
  have hstable : (prefixWord ++ tailWord_2308922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308922).length < 2 ^ (prefixWord ++ tailWord_2308922).sum := by decide
  have hdescent : baseEnd_2308922 < baseStart_2308922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308942 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_2308942 : Nat := 118140960795 + 2308942 * 2 ^ 59
def prefixEnd_2308942 : Nat := 4983230072969 + 3 ^ 40 * 2308942 * 2
def baseEnd_2308942 : Nat := 1185597049353610487506375

theorem tailTrace_2308942 : CollatzResearch.WordTrace tailWord_2308942 prefixEnd_2308942 1185597049353610487506375 := by
  unfold tailWord_2308942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10526754150138118093003135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56142688800736629829350053 10526754150138118093003135)
  ·
    refine ⟨15790131225207177139504703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10526754150138118093003135 15790131225207177139504703)
    ·
      refine ⟨23685196837810765709257055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15790131225207177139504703 23685196837810765709257055)
      ·
        refine ⟨35527795256716148563885583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23685196837810765709257055 35527795256716148563885583)
        ·
          refine ⟨53291692885074222845828375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35527795256716148563885583 53291692885074222845828375)
          ·
            refine ⟨79937539327611334268742563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53291692885074222845828375 79937539327611334268742563)
            ·
              refine ⟨119906308991417001403113845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79937539327611334268742563 119906308991417001403113845)
              ·
                refine ⟨11241216467945343881541923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119906308991417001403113845 11241216467945343881541923)
                ·
                  refine ⟨16861824701918015822312885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11241216467945343881541923 16861824701918015822312885)
                  ·
                    refine ⟨1580796065804813983341833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16861824701918015822312885 1580796065804813983341833)
                    ·
                      refine ⟨1185597049353610487506375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580796065804813983341833 1185597049353610487506375)
                      ·
                        rfl

theorem cell23_2308942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_2308942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308942 prefixEnd_2308942 := by exact prefixLift 2308942
  have htrace : WordTrace (prefixWord ++ tailWord_2308942) baseStart_2308942 baseEnd_2308942 := by
    simpa [prefixWord, tailWord_2308942, baseEnd_2308942] using wordTrace_append hprefix tailTrace_2308942
  have hstable : (prefixWord ++ tailWord_2308942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308942).length < 2 ^ (prefixWord ++ tailWord_2308942).sum := by decide
  have hdescent : baseEnd_2308942 < baseStart_2308942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308975 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_2308975 : Nat := 118140960795 + 2308975 * 2 ^ 59
def prefixEnd_2308975 : Nat := 4983230072969 + 3 ^ 40 * 2308975 * 2
def baseEnd_2308975 : Nat := 1185613994215208858393723

theorem tailTrace_2308975 : CollatzResearch.WordTrace tailWord_2308975 prefixEnd_2308975 1185613994215208858393723 := by
  unfold tailWord_2308975
  simp only [CollatzResearch.WordTrace]
  refine ⟨84215236809985391379976379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56143491206656927586650919 84215236809985391379976379)
  ·
    refine ⟨126322855214978087069964569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84215236809985391379976379 126322855214978087069964569)
    ·
      refine ⟨94742141411233565302473427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126322855214978087069964569 94742141411233565302473427)
      ·
        refine ⟨142113212116850347953710141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94742141411233565302473427 142113212116850347953710141)
        ·
          refine ⟨53292454543818880482641303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142113212116850347953710141 53292454543818880482641303)
          ·
            refine ⟨79938681815728320723961955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53292454543818880482641303 79938681815728320723961955)
            ·
              refine ⟨119908022723592481085942933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79938681815728320723961955 119908022723592481085942933)
              ·
                refine ⟨5620688565168397550903575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119908022723592481085942933 5620688565168397550903575)
                ·
                  refine ⟨8431032847752596326355363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5620688565168397550903575 8431032847752596326355363)
                  ·
                    refine ⟨12646549271628894489533045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8431032847752596326355363 12646549271628894489533045)
                    ·
                      refine ⟨1185613994215208858393723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12646549271628894489533045 1185613994215208858393723)
                      ·
                        rfl

theorem cell23_2308975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_2308975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308975 prefixEnd_2308975 := by exact prefixLift 2308975
  have htrace : WordTrace (prefixWord ++ tailWord_2308975) baseStart_2308975 baseEnd_2308975 := by
    simpa [prefixWord, tailWord_2308975, baseEnd_2308975] using wordTrace_append hprefix tailTrace_2308975
  have hstable : (prefixWord ++ tailWord_2308975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308975).length < 2 ^ (prefixWord ++ tailWord_2308975).sum := by decide
  have hdescent : baseEnd_2308975 < baseStart_2308975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308989 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_2308989 : Nat := 118140960795 + 2308989 * 2 ^ 59
def prefixEnd_2308989 : Nat := 4983230072969 + 3 ^ 40 * 2308989 * 2
def baseEnd_2308989 : Nat := 1185621182944371803618659

theorem tailTrace_2308989 : CollatzResearch.WordTrace tailWord_2308989 prefixEnd_2308989 1185621182944371803618659 := by
  unfold tailWord_2308989
  simp only [CollatzResearch.WordTrace]
  refine ⟨84215747431934671770986021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56143831621289781180657347 84215747431934671770986021)
  ·
    refine ⟨15790452643487750957059879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84215747431934671770986021 15790452643487750957059879)
    ·
      refine ⟨23685678965231626435589819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15790452643487750957059879 23685678965231626435589819)
      ·
        refine ⟨35528518447847439653384729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23685678965231626435589819 35528518447847439653384729)
        ·
          refine ⟨26646388835885579740038547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35528518447847439653384729 26646388835885579740038547)
          ·
            refine ⟨39969583253828369610057821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26646388835885579740038547 39969583253828369610057821)
            ·
              refine ⟨14988593720185638603771683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39969583253828369610057821 14988593720185638603771683)
              ·
                refine ⟨22482890580278457905657525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14988593720185638603771683 22482890580278457905657525)
                ·
                  refine ⟨2107770991901105428655393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22482890580278457905657525 2107770991901105428655393)
                  ·
                    refine ⟨1580828243925829071491545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2107770991901105428655393 1580828243925829071491545)
                    ·
                      refine ⟨1185621182944371803618659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580828243925829071491545 1185621182944371803618659)
                      ·
                        rfl

theorem cell23_2308989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_2308989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2308989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2308989 prefixEnd_2308989 := by exact prefixLift 2308989
  have htrace : WordTrace (prefixWord ++ tailWord_2308989) baseStart_2308989 baseEnd_2308989 := by
    simpa [prefixWord, tailWord_2308989, baseEnd_2308989] using wordTrace_append hprefix tailTrace_2308989
  have hstable : (prefixWord ++ tailWord_2308989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308989).length < 2 ^ (prefixWord ++ tailWord_2308989).sum := by decide
  have hdescent : baseEnd_2308989 < baseStart_2308989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309023 : List Nat := [1, 1, 2, 5, 2, 1, 2, 4, 1, 2, 2]
def baseStart_2309023 : Nat := 118140960795 + 2309023 * 2 ^ 59
def prefixEnd_2309023 : Nat := 4983230072969 + 3 ^ 40 * 2309023 * 2
def baseEnd_2309023 : Nat := 1185638641286624670593503

theorem tailTrace_2309023 : CollatzResearch.WordTrace tailWord_2309023 prefixEnd_2309023 1185638641286624670593503 := by
  unfold tailWord_2309023
  simp only [CollatzResearch.WordTrace]
  refine ⟨84216987513811495577723723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56144658342540997051815815 84216987513811495577723723)
  ·
    refine ⟨126325481270717243366585585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84216987513811495577723723 126325481270717243366585585)
    ·
      refine ⟨94744110953037932524939189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126325481270717243366585585 94744110953037932524939189)
      ·
        refine ⟨8882260401847306174213049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94744110953037932524939189 8882260401847306174213049)
        ·
          refine ⟨6661695301385479630659787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8882260401847306174213049 6661695301385479630659787)
          ·
            refine ⟨9992542952078219445989681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6661695301385479630659787 9992542952078219445989681)
            ·
              refine ⟨7494407214058664584492261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9992542952078219445989681 7494407214058664584492261)
              ·
                refine ⟨1405201352635999609592299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7494407214058664584492261 1405201352635999609592299)
                ·
                  refine ⟨2107802028953999414388449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405201352635999609592299 2107802028953999414388449)
                  ·
                    refine ⟨1580851521715499560791337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2107802028953999414388449 1580851521715499560791337)
                    ·
                      refine ⟨1185638641286624670593503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580851521715499560791337 1185638641286624670593503)
                      ·
                        rfl

theorem cell23_2309023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_2309023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309023 prefixEnd_2309023 := by exact prefixLift 2309023
  have htrace : WordTrace (prefixWord ++ tailWord_2309023) baseStart_2309023 baseEnd_2309023 := by
    simpa [prefixWord, tailWord_2309023, baseEnd_2309023] using wordTrace_append hprefix tailTrace_2309023
  have hstable : (prefixWord ++ tailWord_2309023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309023).length < 2 ^ (prefixWord ++ tailWord_2309023).sum := by decide
  have hdescent : baseEnd_2309023 < baseStart_2309023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309055 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 4, 6]
def baseStart_2309055 : Nat := 118140960795 + 2309055 * 2 ^ 59
def prefixEnd_2309055 : Nat := 4983230072969 + 3 ^ 40 * 2309055 * 2
def baseEnd_2309055 : Nat := 395218357555856181797785

theorem tailTrace_2309055 : CollatzResearch.WordTrace tailWord_2309055 prefixEnd_2309055 395218357555856181797785 := by
  unfold tailWord_2309055
  simp only [CollatzResearch.WordTrace]
  refine ⟨84218154649695565042888619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56145436433130376695259079 84218154649695565042888619)
  ·
    refine ⟨126327231974543347564332929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84218154649695565042888619 126327231974543347564332929)
    ·
      refine ⟨94745423980907510673249697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126327231974543347564332929 94745423980907510673249697)
      ·
        refine ⟨71059067985680633004937273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94745423980907510673249697 71059067985680633004937273)
        ·
          refine ⟨53294300989260474753702955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71059067985680633004937273 53294300989260474753702955)
          ·
            refine ⟨79941451483890712130554433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53294300989260474753702955 79941451483890712130554433)
            ·
              refine ⟨59956088612918034097915825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79941451483890712130554433 59956088612918034097915825)
              ·
                refine ⟨44967066459688525573436869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59956088612918034097915825 44967066459688525573436869)
                ·
                  refine ⟨8431324961191598545019413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44967066459688525573436869 8431324961191598545019413)
                  ·
                    refine ⟨395218357555856181797785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8431324961191598545019413 395218357555856181797785)
                    ·
                      rfl

theorem cell23_2309055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_2309055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309055 prefixEnd_2309055 := by exact prefixLift 2309055
  have htrace : WordTrace (prefixWord ++ tailWord_2309055) baseStart_2309055 baseEnd_2309055 := by
    simpa [prefixWord, tailWord_2309055, baseEnd_2309055] using wordTrace_append hprefix tailTrace_2309055
  have hstable : (prefixWord ++ tailWord_2309055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309055).length < 2 ^ (prefixWord ++ tailWord_2309055).sum := by decide
  have hdescent : baseEnd_2309055 < baseStart_2309055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309090 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2309090 : Nat := 118140960795 + 2309090 * 2 ^ 59
def prefixEnd_2309090 : Nat := 4983230072969 + 3 ^ 40 * 2309090 * 2
def baseEnd_2309090 : Nat := 1185673044490475908455695

theorem tailTrace_2309090 : CollatzResearch.WordTrace tailWord_2309090 prefixEnd_2309090 1185673044490475908455695 := by
  unfold tailWord_2309090
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054857801142191505103181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56146287469712510680275149 21054857801142191505103181)
  ·
    refine ⟨7895571675428321814413693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21054857801142191505103181 7895571675428321814413693)
    ·
      refine ⟨2960839378285620680405135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7895571675428321814413693 2960839378285620680405135)
      ·
        refine ⟨4441259067428431020607703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960839378285620680405135 4441259067428431020607703)
        ·
          refine ⟨6661888601142646530911555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441259067428431020607703 6661888601142646530911555)
          ·
            refine ⟨9992832901713969796367333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6661888601142646530911555 9992832901713969796367333)
            ·
              refine ⟨1873656169071369336818875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9992832901713969796367333 1873656169071369336818875)
              ·
                refine ⟨2810484253607054005228313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873656169071369336818875 2810484253607054005228313)
                ·
                  refine ⟨2107863190205290503921235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2810484253607054005228313 2107863190205290503921235)
                  ·
                    refine ⟨3161794785307935755881853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2107863190205290503921235 3161794785307935755881853)
                    ·
                      refine ⟨1185673044490475908455695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3161794785307935755881853 1185673044490475908455695)
                      ·
                        rfl

theorem cell23_2309090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2309090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309090 prefixEnd_2309090 := by exact prefixLift 2309090
  have htrace : WordTrace (prefixWord ++ tailWord_2309090) baseStart_2309090 baseEnd_2309090 := by
    simpa [prefixWord, tailWord_2309090, baseEnd_2309090] using wordTrace_append hprefix tailTrace_2309090
  have hstable : (prefixWord ++ tailWord_2309090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309090).length < 2 ^ (prefixWord ++ tailWord_2309090).sum := by decide
  have hdescent : baseEnd_2309090 < baseStart_2309090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309112 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_2309112 : Nat := 118140960795 + 2309112 * 2 ^ 59
def prefixEnd_2309112 : Nat := 4983230072969 + 3 ^ 40 * 2309112 * 2
def baseEnd_2309112 : Nat := 1185684341064874822380593

theorem tailTrace_2309112 : CollatzResearch.WordTrace tailWord_2309112 prefixEnd_2309112 1185684341064874822380593 := by
  unfold tailWord_2309112
  simp only [CollatzResearch.WordTrace]
  refine ⟨42110116805244531888856795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56146822406992709185142393 42110116805244531888856795)
  ·
    refine ⟨63165175207866797833285193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42110116805244531888856795 63165175207866797833285193)
    ·
      refine ⟨47373881405900098374963895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63165175207866797833285193 47373881405900098374963895)
      ·
        refine ⟨71060822108850147562445843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47373881405900098374963895 71060822108850147562445843)
        ·
          refine ⟨106591233163275221343668765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71060822108850147562445843 106591233163275221343668765)
          ·
            refine ⟨39971712436228208003875787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106591233163275221343668765 39971712436228208003875787)
            ·
              refine ⟨59957568654342312005813681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39971712436228208003875787 59957568654342312005813681)
              ·
                refine ⟨44968176490756734004360261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59957568654342312005813681 44968176490756734004360261)
                ·
                  refine ⟨8431533092016887625817549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44968176490756734004360261 8431533092016887625817549)
                  ·
                    refine ⟨3161824909506332859681581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8431533092016887625817549 3161824909506332859681581)
                    ·
                      refine ⟨1185684341064874822380593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3161824909506332859681581 1185684341064874822380593)
                      ·
                        rfl

theorem cell23_2309112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_2309112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309112 prefixEnd_2309112 := by exact prefixLift 2309112
  have htrace : WordTrace (prefixWord ++ tailWord_2309112) baseStart_2309112 baseEnd_2309112 := by
    simpa [prefixWord, tailWord_2309112, baseEnd_2309112] using wordTrace_append hprefix tailTrace_2309112
  have hstable : (prefixWord ++ tailWord_2309112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309112).length < 2 ^ (prefixWord ++ tailWord_2309112).sum := by decide
  have hdescent : baseEnd_2309112 < baseStart_2309112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309169 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 1, 6, 2]
def baseStart_2309169 : Nat := 118140960795 + 2309169 * 2 ^ 59
def prefixEnd_2309169 : Nat := 4983230072969 + 3 ^ 40 * 2309169 * 2
def baseEnd_2309169 : Nat := 1185713609462181099367831

theorem tailTrace_2309169 : CollatzResearch.WordTrace tailWord_2309169 prefixEnd_2309169 1185713609462181099367831 := by
  unfold tailWord_2309169
  simp only [CollatzResearch.WordTrace]
  refine ⟨84222312571282562512538561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56148208380855041675025707 84222312571282562512538561)
  ·
    refine ⟨63166734428461921884403921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84222312571282562512538561 63166734428461921884403921)
    ·
      refine ⟨47375050821346441413302941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63166734428461921884403921 47375050821346441413302941)
      ·
        refine ⟨17765644058004915529988603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47375050821346441413302941 17765644058004915529988603)
        ·
          refine ⟨26648466087007373294982905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17765644058004915529988603 26648466087007373294982905)
          ·
            refine ⟨19986349565255529971237179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26648466087007373294982905 19986349565255529971237179)
            ·
              refine ⟨29979524347883294956855769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19986349565255529971237179 29979524347883294956855769)
              ·
                refine ⟨22484643260912471217641827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29979524347883294956855769 22484643260912471217641827)
                ·
                  refine ⟨33726964891368706826462741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22484643260912471217641827 33726964891368706826462741)
                  ·
                    refine ⟨1580951479282908132490441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33726964891368706826462741 1580951479282908132490441)
                    ·
                      refine ⟨1185713609462181099367831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1580951479282908132490441 1185713609462181099367831)
                      ·
                        rfl

theorem cell23_2309169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_2309169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309169 prefixEnd_2309169 := by exact prefixLift 2309169
  have htrace : WordTrace (prefixWord ++ tailWord_2309169) baseStart_2309169 baseEnd_2309169 := by
    simpa [prefixWord, tailWord_2309169, baseEnd_2309169] using wordTrace_append hprefix tailTrace_2309169
  have hstable : (prefixWord ++ tailWord_2309169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309169).length < 2 ^ (prefixWord ++ tailWord_2309169).sum := by decide
  have hdescent : baseEnd_2309169 < baseStart_2309169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309189 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_2309189 : Nat := 118140960795 + 2309189 * 2 ^ 59
def prefixEnd_2309189 : Nat := 4983230072969 + 3 ^ 40 * 2309189 * 2
def baseEnd_2309189 : Nat := 1185723879075271021117739

theorem tailTrace_2309189 : CollatzResearch.WordTrace tailWord_2309189 prefixEnd_2309189 1185723879075271021117739 := by
  unfold tailWord_2309189
  simp only [CollatzResearch.WordTrace]
  refine ⟨84223042031210105928266621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56148694687473403952177747 84223042031210105928266621)
  ·
    refine ⟨31583640761703789723099983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84223042031210105928266621 31583640761703789723099983)
    ·
      refine ⟨47375461142555684584649975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31583640761703789723099983 47375461142555684584649975)
      ·
        refine ⟨71063191713833526876974963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47375461142555684584649975 71063191713833526876974963)
        ·
          refine ⟨106594787570750290315462445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71063191713833526876974963 106594787570750290315462445)
          ·
            refine ⟨39973045339031358868298417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106594787570750290315462445 39973045339031358868298417)
            ·
              refine ⟨29979784004273519151223813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39973045339031358868298417 29979784004273519151223813)
              ·
                refine ⟨5621209500801284840854465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29979784004273519151223813 5621209500801284840854465)
                ·
                  refine ⟨4215907125600963630640849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5621209500801284840854465 4215907125600963630640849)
                  ·
                    refine ⟨3161930344200722722980637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4215907125600963630640849 3161930344200722722980637)
                    ·
                      refine ⟨1185723879075271021117739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3161930344200722722980637 1185723879075271021117739)
                      ·
                        rfl

theorem cell23_2309189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_2309189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309189 prefixEnd_2309189 := by exact prefixLift 2309189
  have htrace : WordTrace (prefixWord ++ tailWord_2309189) baseStart_2309189 baseEnd_2309189 := by
    simpa [prefixWord, tailWord_2309189, baseEnd_2309189] using wordTrace_append hprefix tailTrace_2309189
  have hstable : (prefixWord ++ tailWord_2309189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309189).length < 2 ^ (prefixWord ++ tailWord_2309189).sum := by decide
  have hdescent : baseEnd_2309189 < baseStart_2309189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309192 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 8]
def baseStart_2309192 : Nat := 118140960795 + 2309192 * 2 ^ 59
def prefixEnd_2309192 : Nat := 4983230072969 + 3 ^ 40 * 2309192 * 2
def baseEnd_2309192 : Nat := 131747268835248278820025

theorem tailTrace_2309192 : CollatzResearch.WordTrace tailWord_2309192 prefixEnd_2309192 131747268835248278820025 := by
  unfold tailWord_2309192
  simp only [CollatzResearch.WordTrace]
  refine ⟨42111575725099618720312915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56148767633466158293750553 42111575725099618720312915)
  ·
    refine ⟨63167363587649428080469373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42111575725099618720312915 63167363587649428080469373)
    ·
      refine ⟨23687761345368535530176015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63167363587649428080469373 23687761345368535530176015)
      ·
        refine ⟨35531642018052803295264023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23687761345368535530176015 35531642018052803295264023)
        ·
          refine ⟨53297463027079204942896035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35531642018052803295264023 53297463027079204942896035)
          ·
            refine ⟨79946194540618807414344053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53297463027079204942896035 79946194540618807414344053)
            ·
              refine ⟨7494955738183013195094755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79946194540618807414344053 7494955738183013195094755)
              ·
                refine ⟨11242433607274519792642133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7494955738183013195094755 11242433607274519792642133)
                ·
                  refine ⟨131747268835248278820025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11242433607274519792642133 131747268835248278820025)
                  ·
                    rfl

theorem cell23_2309192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 8].length) (baseStart_2309192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309192 prefixEnd_2309192 := by exact prefixLift 2309192
  have htrace : WordTrace (prefixWord ++ tailWord_2309192) baseStart_2309192 baseEnd_2309192 := by
    simpa [prefixWord, tailWord_2309192, baseEnd_2309192] using wordTrace_append hprefix tailTrace_2309192
  have hstable : (prefixWord ++ tailWord_2309192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309192).length < 2 ^ (prefixWord ++ tailWord_2309192).sum := by decide
  have hdescent : baseEnd_2309192 < baseStart_2309192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309230 : List Nat := [4, 1, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_2309230 : Nat := 118140960795 + 2309230 * 2 ^ 59
def prefixEnd_2309230 : Nat := 4983230072969 + 3 ^ 40 * 2309230 * 2
def baseEnd_2309230 : Nat := 395248310594035120235017

theorem tailTrace_2309230 : CollatzResearch.WordTrace tailWord_2309230 prefixEnd_2309230 395248310594035120235017 := by
  unfold tailWord_2309230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10528067178007696241313643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56149691616041046620339429 10528067178007696241313643)
  ·
    refine ⟨15792100767011544361970465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10528067178007696241313643 15792100767011544361970465)
    ·
      refine ⟨11844075575258658271477849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15792100767011544361970465 11844075575258658271477849)
      ·
        refine ⟨8883056681443993703608387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11844075575258658271477849 8883056681443993703608387)
        ·
          refine ⟨13324585022165990555412581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8883056681443993703608387 13324585022165990555412581)
          ·
            refine ⟨2498359691656123229139859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13324585022165990555412581 2498359691656123229139859)
            ·
              refine ⟨3747539537484184843709789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498359691656123229139859 3747539537484184843709789)
              ·
                refine ⟨1405327326556569316391171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3747539537484184843709789 1405327326556569316391171)
                ·
                  refine ⟨2107990989834853974586757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405327326556569316391171 2107990989834853974586757)
                  ·
                    refine ⟨395248310594035120235017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2107990989834853974586757 395248310594035120235017)
                    ·
                      rfl

theorem cell23_2309230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_2309230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309230 prefixEnd_2309230 := by exact prefixLift 2309230
  have htrace : WordTrace (prefixWord ++ tailWord_2309230) baseStart_2309230 baseEnd_2309230 := by
    simpa [prefixWord, tailWord_2309230, baseEnd_2309230] using wordTrace_append hprefix tailTrace_2309230
  have hstable : (prefixWord ++ tailWord_2309230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309230).length < 2 ^ (prefixWord ++ tailWord_2309230).sum := by decide
  have hdescent : baseEnd_2309230 < baseStart_2309230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309239 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 1, 5]
def baseStart_2309239 : Nat := 118140960795 + 2309239 * 2 ^ 59
def prefixEnd_2309239 : Nat := 4983230072969 + 3 ^ 40 * 2309239 * 2
def baseEnd_2309239 : Nat := 395249851035998608497503

theorem tailTrace_2309239 : CollatzResearch.WordTrace tailWord_2309239 prefixEnd_2309239 395249851035998608497503 := by
  unfold tailWord_2309239
  simp only [CollatzResearch.WordTrace]
  refine ⟨84224865681028964467586771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56149910454019309645057847 84224865681028964467586771)
  ·
    refine ⟨126337298521543446701380157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84224865681028964467586771 126337298521543446701380157)
    ·
      refine ⟨47376486945578792513017559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126337298521543446701380157 47376486945578792513017559)
      ·
        refine ⟨71064730418368188769526339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47376486945578792513017559 71064730418368188769526339)
        ·
          refine ⟨106597095627552283154289509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71064730418368188769526339 106597095627552283154289509)
          ·
            refine ⟨19986955430166053091429283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106597095627552283154289509 19986955430166053091429283)
            ·
              refine ⟨29980433145249079637143925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19986955430166053091429283 29980433145249079637143925)
              ·
                refine ⟨2810665607367101215982243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29980433145249079637143925 2810665607367101215982243)
                ·
                  refine ⟨4215998411050651823973365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810665607367101215982243 4215998411050651823973365)
                  ·
                    refine ⟨395249851035998608497503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4215998411050651823973365 395249851035998608497503)
                    ·
                      rfl

theorem cell23_2309239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_2309239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309239 prefixEnd_2309239 := by exact prefixLift 2309239
  have htrace : WordTrace (prefixWord ++ tailWord_2309239) baseStart_2309239 baseEnd_2309239 := by
    simpa [prefixWord, tailWord_2309239, baseEnd_2309239] using wordTrace_append hprefix tailTrace_2309239
  have hstable : (prefixWord ++ tailWord_2309239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309239).length < 2 ^ (prefixWord ++ tailWord_2309239).sum := by decide
  have hdescent : baseEnd_2309239 < baseStart_2309239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309269 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_2309269 : Nat := 118140960795 + 2309269 * 2 ^ 59
def prefixEnd_2309269 : Nat := 4983230072969 + 3 ^ 40 * 2309269 * 2
def baseEnd_2309269 : Nat := 395254985842543569372457

theorem tailTrace_2309269 : CollatzResearch.WordTrace tailWord_2309269 prefixEnd_2309269 395254985842543569372457 := by
  unfold tailWord_2309269
  simp only [CollatzResearch.WordTrace]
  refine ⟨84225959870920279591178861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56150639913946853060785907 84225959870920279591178861)
  ·
    refine ⟨31584734951595104846692073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84225959870920279591178861 31584734951595104846692073)
    ·
      refine ⟨23688551213696328635019055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31584734951595104846692073 23688551213696328635019055)
      ·
        refine ⟨35532826820544492952528583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23688551213696328635019055 35532826820544492952528583)
        ·
          refine ⟨53299240230816739428792875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35532826820544492952528583 53299240230816739428792875)
          ·
            refine ⟨79948860346225109143189313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53299240230816739428792875 79948860346225109143189313)
            ·
              refine ⟨59961645259668831857391985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79948860346225109143189313 59961645259668831857391985)
              ·
                refine ⟨44971233944751623893043989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59961645259668831857391985 44971233944751623893043989)
                ·
                  refine ⟨2108026591160232369986437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44971233944751623893043989 2108026591160232369986437)
                  ·
                    refine ⟨395254985842543569372457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2108026591160232369986437 395254985842543569372457)
                    ·
                      rfl

theorem cell23_2309269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_2309269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309269 prefixEnd_2309269 := by exact prefixLift 2309269
  have htrace : WordTrace (prefixWord ++ tailWord_2309269) baseStart_2309269 baseEnd_2309269 := by
    simpa [prefixWord, tailWord_2309269, baseEnd_2309269] using wordTrace_append hprefix tailTrace_2309269
  have hstable : (prefixWord ++ tailWord_2309269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309269).length < 2 ^ (prefixWord ++ tailWord_2309269).sum := by decide
  have hdescent : baseEnd_2309269 < baseStart_2309269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309276 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2309276 : Nat := 118140960795 + 2309276 * 2 ^ 59
def prefixEnd_2309276 : Nat := 4983230072969 + 3 ^ 40 * 2309276 * 2
def baseEnd_2309276 : Nat := 1185768551892212180729839

theorem tailTrace_2309276 : CollatzResearch.WordTrace tailWord_2309276 prefixEnd_2309276 1185768551892212180729839 := by
  unfold tailWord_2309276
  simp only [CollatzResearch.WordTrace]
  refine ⟨42113107590947459893341841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56150810121263279857789121 42113107590947459893341841)
  ·
    refine ⟨31584830693210594920006381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42113107590947459893341841 31584830693210594920006381)
    ·
      refine ⟨11844311509953973095002393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31584830693210594920006381 11844311509953973095002393)
      ·
        refine ⟨8883233632465479821251795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11844311509953973095002393 8883233632465479821251795)
        ·
          refine ⟨13324850448698219731877693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8883233632465479821251795 13324850448698219731877693)
          ·
            refine ⟨4996818918261832399454135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13324850448698219731877693 4996818918261832399454135)
            ·
              refine ⟨7495228377392748599181203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4996818918261832399454135 7495228377392748599181203)
              ·
                refine ⟨11242842566089122898771805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7495228377392748599181203 11242842566089122898771805)
                ·
                  refine ⟨4216065962283421087039427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11242842566089122898771805 4216065962283421087039427)
                  ·
                    refine ⟨6324098943425131630559141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4216065962283421087039427 6324098943425131630559141)
                    ·
                      refine ⟨1185768551892212180729839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6324098943425131630559141 1185768551892212180729839)
                      ·
                        rfl

theorem cell23_2309276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2309276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309276 prefixEnd_2309276 := by exact prefixLift 2309276
  have htrace : WordTrace (prefixWord ++ tailWord_2309276) baseStart_2309276 baseEnd_2309276 := by
    simpa [prefixWord, tailWord_2309276, baseEnd_2309276] using wordTrace_append hprefix tailTrace_2309276
  have hstable : (prefixWord ++ tailWord_2309276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309276).length < 2 ^ (prefixWord ++ tailWord_2309276).sum := by decide
  have hdescent : baseEnd_2309276 < baseStart_2309276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309290 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2309290 : Nat := 118140960795 + 2309290 * 2 ^ 59
def prefixEnd_2309290 : Nat := 4983230072969 + 3 ^ 40 * 2309290 * 2
def baseEnd_2309290 : Nat := 395258580207125041984925

theorem tailTrace_2309290 : CollatzResearch.WordTrace tailWord_2309290 prefixEnd_2309290 395258580207125041984925 := by
  unfold tailWord_2309290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21056681450961050044423331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56151150535896133451795549 21056681450961050044423331)
  ·
    refine ⟨31585022176441575066634997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21056681450961050044423331 31585022176441575066634997)
    ·
      refine ⟨2961095829041397662497031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31585022176441575066634997 2961095829041397662497031)
      ·
        refine ⟨4441643743562096493745547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961095829041397662497031 4441643743562096493745547)
        ·
          refine ⟨6662465615343144740618321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441643743562096493745547 6662465615343144740618321)
          ·
            refine ⟨4996849211507358555463741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6662465615343144740618321 4996849211507358555463741)
            ·
              refine ⟨1873818454315259458298903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4996849211507358555463741 1873818454315259458298903)
              ·
                refine ⟨2810727681472889187448355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873818454315259458298903 2810727681472889187448355)
                ·
                  refine ⟨4216091522209333781172533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810727681472889187448355 4216091522209333781172533)
                  ·
                    refine ⟨395258580207125041984925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4216091522209333781172533 395258580207125041984925)
                    ·
                      rfl

theorem cell23_2309290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2309290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309290 prefixEnd_2309290 := by exact prefixLift 2309290
  have htrace : WordTrace (prefixWord ++ tailWord_2309290) baseStart_2309290 baseEnd_2309290 := by
    simpa [prefixWord, tailWord_2309290, baseEnd_2309290] using wordTrace_append hprefix tailTrace_2309290
  have hstable : (prefixWord ++ tailWord_2309290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309290).length < 2 ^ (prefixWord ++ tailWord_2309290).sum := by decide
  have hdescent : baseEnd_2309290 < baseStart_2309290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309313 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2309313 : Nat := 118140960795 + 2309313 * 2 ^ 59
def prefixEnd_2309313 : Nat := 4983230072969 + 3 ^ 40 * 2309313 * 2
def baseEnd_2309313 : Nat := 1185787550676428535967169

theorem tailTrace_2309313 : CollatzResearch.WordTrace tailWord_2309313 prefixEnd_2309313 1185787550676428535967169 := by
  unfold tailWord_2309313
  simp only [CollatzResearch.WordTrace]
  refine ⟨84227564682760875105780593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56151709788507250070520395 84227564682760875105780593)
  ·
    refine ⟨63170673512070656329335445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84227564682760875105780593 63170673512070656329335445)
    ·
      refine ⟨2961125320878312015437599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63170673512070656329335445 2961125320878312015437599)
      ·
        refine ⟨4441687981317468023156399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961125320878312015437599 4441687981317468023156399)
        ·
          refine ⟨6662531971976202034734599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441687981317468023156399 6662531971976202034734599)
          ·
            refine ⟨9993797957964303052101899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6662531971976202034734599 9993797957964303052101899)
            ·
              refine ⟨14990696936946454578152849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9993797957964303052101899 14990696936946454578152849)
              ·
                refine ⟨11243022702709840933614637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14990696936946454578152849 11243022702709840933614637)
                ·
                  refine ⟨4216133513516190350105489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11243022702709840933614637 4216133513516190350105489)
                  ·
                    refine ⟨3162100135137142762579117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4216133513516190350105489 3162100135137142762579117)
                    ·
                      refine ⟨1185787550676428535967169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3162100135137142762579117 1185787550676428535967169)
                      ·
                        rfl

theorem cell23_2309313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2309313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309313 prefixEnd_2309313 := by exact prefixLift 2309313
  have htrace : WordTrace (prefixWord ++ tailWord_2309313) baseStart_2309313 baseEnd_2309313 := by
    simpa [prefixWord, tailWord_2309313, baseEnd_2309313] using wordTrace_append hprefix tailTrace_2309313
  have hstable : (prefixWord ++ tailWord_2309313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309313).length < 2 ^ (prefixWord ++ tailWord_2309313).sum := by decide
  have hdescent : baseEnd_2309313 < baseStart_2309313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309449 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 2, 8]
def baseStart_2309449 : Nat := 118140960795 + 2309449 * 2 ^ 59
def prefixEnd_2309449 : Nat := 4983230072969 + 3 ^ 40 * 2309449 * 2
def baseEnd_2309449 : Nat := 395285794681813334622181

theorem tailTrace_2309449 : CollatzResearch.WordTrace tailWord_2309449 prefixEnd_2309449 395285794681813334622181 := by
  unfold tailWord_2309449
  simp only [CollatzResearch.WordTrace]
  refine ⟨84232525010268170332731401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56155016673512113555154267 84232525010268170332731401)
  ·
    refine ⟨63174393757701127749548551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84232525010268170332731401 63174393757701127749548551)
    ·
      refine ⟨94761590636551691624322827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63174393757701127749548551 94761590636551691624322827)
      ·
        refine ⟨142142385954827537436484241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94761590636551691624322827 142142385954827537436484241)
        ·
          refine ⟨106606789466120653077363181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142142385954827537436484241 106606789466120653077363181)
          ·
            refine ⟨39977546049795244904011193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106606789466120653077363181 39977546049795244904011193)
            ·
              refine ⟨29983159537346433678008395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39977546049795244904011193 29983159537346433678008395)
              ·
                refine ⟨44974739306019650517012593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29983159537346433678008395 44974739306019650517012593)
                ·
                  refine ⟨33731054479514737887759445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44974739306019650517012593 33731054479514737887759445)
                  ·
                    refine ⟨395285794681813334622181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33731054479514737887759445 395285794681813334622181)
                    ·
                      rfl

theorem cell23_2309449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_2309449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309449 prefixEnd_2309449 := by exact prefixLift 2309449
  have htrace : WordTrace (prefixWord ++ tailWord_2309449) baseStart_2309449 baseEnd_2309449 := by
    simpa [prefixWord, tailWord_2309449, baseEnd_2309449] using wordTrace_append hprefix tailTrace_2309449
  have hstable : (prefixWord ++ tailWord_2309449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309449).length < 2 ^ (prefixWord ++ tailWord_2309449).sum := by decide
  have hdescent : baseEnd_2309449 < baseStart_2309449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309580 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2309580 : Nat := 118140960795 + 2309580 * 2 ^ 59
def prefixEnd_2309580 : Nat := 4983230072969 + 3 ^ 40 * 2309580 * 2
def baseEnd_2309580 : Nat := 1185924650011178991328441

theorem tailTrace_2309580 : CollatzResearch.WordTrace tailWord_2309580 prefixEnd_2309580 1185924650011178991328441 := by
  unfold tailWord_2309580
  simp only [CollatzResearch.WordTrace]
  refine ⟨42118651486396789852875097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56158201981862386470500129 42118651486396789852875097)
  ·
    refine ⟨31588988614797592389656323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42118651486396789852875097 31588988614797592389656323)
    ·
      refine ⟨47383482922196388584484485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31588988614797592389656323 47383482922196388584484485)
      ·
        refine ⟨8884403047911822859590841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47383482922196388584484485 8884403047911822859590841)
        ·
          refine ⟨6663302285933867144693131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8884403047911822859590841 6663302285933867144693131)
          ·
            refine ⟨9994953428900800717039697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6663302285933867144693131 9994953428900800717039697)
            ·
              refine ⟨7496215071675600537779773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9994953428900800717039697 7496215071675600537779773)
              ·
                refine ⟨2811080651878350201667415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7496215071675600537779773 2811080651878350201667415)
                ·
                  refine ⟨4216620977817525302501123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811080651878350201667415 4216620977817525302501123)
                  ·
                    refine ⟨6324931466726287953751685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4216620977817525302501123 6324931466726287953751685)
                    ·
                      refine ⟨1185924650011178991328441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6324931466726287953751685 1185924650011178991328441)
                      ·
                        rfl

theorem cell23_2309580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2309580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309580 prefixEnd_2309580 := by exact prefixLift 2309580
  have htrace : WordTrace (prefixWord ++ tailWord_2309580) baseStart_2309580 baseEnd_2309580 := by
    simpa [prefixWord, tailWord_2309580, baseEnd_2309580] using wordTrace_append hprefix tailTrace_2309580
  have hstable : (prefixWord ++ tailWord_2309580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309580).length < 2 ^ (prefixWord ++ tailWord_2309580).sum := by decide
  have hdescent : baseEnd_2309580 < baseStart_2309580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309603 : List Nat := [1, 1, 1, 6, 2, 2, 2, 8]
def baseStart_2309603 : Nat := 118140960795 + 2309603 * 2 ^ 59
def prefixEnd_2309603 : Nat := 4983230072969 + 3 ^ 40 * 2309603 * 2
def baseEnd_2309603 : Nat := 43923572595045644494105

theorem tailTrace_2309603 : CollatzResearch.WordTrace tailWord_2309603 prefixEnd_2309603 43923572595045644494105 := by
  unfold tailWord_2309603
  simp only [CollatzResearch.WordTrace]
  refine ⟨84238141851710254633837463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56158761234473503089224975 84238141851710254633837463)
  ·
    refine ⟨126357212777565381950756195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84238141851710254633837463 126357212777565381950756195)
    ·
      refine ⟨189535819166348072926134293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126357212777565381950756195 189535819166348072926134293)
      ·
        refine ⟨8884491523422565918412545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 189535819166348072926134293 8884491523422565918412545)
        ·
          refine ⟨6663368642566924438809409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8884491523422565918412545 6663368642566924438809409)
          ·
            refine ⟨4997526481925193329107057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6663368642566924438809409 4997526481925193329107057)
            ·
              refine ⟨3748144861443894996830293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4997526481925193329107057 3748144861443894996830293)
              ·
                refine ⟨43923572595045644494105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3748144861443894996830293 43923572595045644494105)
                ·
                  rfl

theorem cell23_2309603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 8].length) (baseStart_2309603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309603 prefixEnd_2309603 := by exact prefixLift 2309603
  have htrace : WordTrace (prefixWord ++ tailWord_2309603) baseStart_2309603 baseEnd_2309603 := by
    simpa [prefixWord, tailWord_2309603, baseEnd_2309603] using wordTrace_append hprefix tailTrace_2309603
  have hstable : (prefixWord ++ tailWord_2309603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309603).length < 2 ^ (prefixWord ++ tailWord_2309603).sum := by decide
  have hdescent : baseEnd_2309603 < baseStart_2309603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309607 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 2, 4]
def baseStart_2309607 : Nat := 118140960795 + 2309607 * 2 ^ 59
def prefixEnd_2309607 : Nat := 4983230072969 + 3 ^ 40 * 2309607 * 2
def baseEnd_2309607 : Nat := 395312837996283461896939

theorem tailTrace_2309607 : CollatzResearch.WordTrace tailWord_2309607 prefixEnd_2309607 395312837996283461896939 := by
  unfold tailWord_2309607
  simp only [CollatzResearch.WordTrace]
  refine ⟨84238287743695763316983075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56158858495797175544655383 84238287743695763316983075)
  ·
    refine ⟨126357431615543644975474613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84238287743695763316983075 126357431615543644975474613)
    ·
      refine ⟨11846009213957216716450745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126357431615543644975474613 11846009213957216716450745)
      ·
        refine ⟨8884506910467912537338059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11846009213957216716450745 8884506910467912537338059)
        ·
          refine ⟨13326760365701868806007089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8884506910467912537338059 13326760365701868806007089)
          ·
            refine ⟨9995070274276401604505317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13326760365701868806007089 9995070274276401604505317)
            ·
              refine ⟨1874075676426825300844747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9995070274276401604505317 1874075676426825300844747)
              ·
                refine ⟨2811113514640237951267121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874075676426825300844747 2811113514640237951267121)
                ·
                  refine ⟨2108335135980178463450341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2811113514640237951267121 2108335135980178463450341)
                  ·
                    refine ⟨395312837996283461896939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2108335135980178463450341 395312837996283461896939)
                    ·
                      rfl

theorem cell23_2309607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_2309607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309607 prefixEnd_2309607 := by exact prefixLift 2309607
  have htrace : WordTrace (prefixWord ++ tailWord_2309607) baseStart_2309607 baseEnd_2309607 := by
    simpa [prefixWord, tailWord_2309607, baseEnd_2309607] using wordTrace_append hprefix tailTrace_2309607
  have hstable : (prefixWord ++ tailWord_2309607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309607).length < 2 ^ (prefixWord ++ tailWord_2309607).sum := by decide
  have hdescent : baseEnd_2309607 < baseStart_2309607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309617 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_2309617 : Nat := 118140960795 + 2309617 * 2 ^ 59
def prefixEnd_2309617 : Nat := 4983230072969 + 3 ^ 40 * 2309617 * 2
def baseEnd_2309617 : Nat := 1185943648795395346565771

theorem tailTrace_2309617 : CollatzResearch.WordTrace tailWord_2309617 prefixEnd_2309617 1185943648795395346565771 := by
  unfold tailWord_2309617
  simp only [CollatzResearch.WordTrace]
  refine ⟨84238652473659535024847105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56159101649106356683231403 84238652473659535024847105)
  ·
    refine ⟨63178989355244651268635329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84238652473659535024847105 63178989355244651268635329)
    ·
      refine ⟨47384242016433488451476497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63178989355244651268635329 47384242016433488451476497)
      ·
        refine ⟨35538181512325116338607373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47384242016433488451476497 35538181512325116338607373)
        ·
          refine ⟨13326818067121918626977765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35538181512325116338607373 13326818067121918626977765)
          ·
            refine ⟨2498778387585359742558331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13326818067121918626977765 2498778387585359742558331)
            ·
              refine ⟨3748167581378039613837497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498778387585359742558331 3748167581378039613837497)
              ·
                refine ⟨2811125686033529710378123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3748167581378039613837497 2811125686033529710378123)
                ·
                  refine ⟨4216688529050294565567185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811125686033529710378123 4216688529050294565567185)
                  ·
                    refine ⟨3162516396787720924175389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4216688529050294565567185 3162516396787720924175389)
                    ·
                      refine ⟨1185943648795395346565771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3162516396787720924175389 1185943648795395346565771)
                      ·
                        rfl

theorem cell23_2309617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_2309617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309617 prefixEnd_2309617 := by exact prefixLift 2309617
  have htrace : WordTrace (prefixWord ++ tailWord_2309617) baseStart_2309617 baseEnd_2309617 := by
    simpa [prefixWord, tailWord_2309617, baseEnd_2309617] using wordTrace_append hprefix tailTrace_2309617
  have hstable : (prefixWord ++ tailWord_2309617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309617).length < 2 ^ (prefixWord ++ tailWord_2309617).sum := by decide
  have hdescent : baseEnd_2309617 < baseStart_2309617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309653 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_2309653 : Nat := 118140960795 + 2309653 * 2 ^ 59
def prefixEnd_2309653 : Nat := 4983230072969 + 3 ^ 40 * 2309653 * 2
def baseEnd_2309653 : Nat := 1185962134098957205715605

theorem tailTrace_2309653 : CollatzResearch.WordTrace tailWord_2309653 prefixEnd_2309653 1185962134098957205715605 := by
  unfold tailWord_2309653
  simp only [CollatzResearch.WordTrace]
  refine ⟨84239965501529113173157613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56159977001019408782105075 84239965501529113173157613)
  ·
    refine ⟨31589987063073417439934105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84239965501529113173157613 31589987063073417439934105)
    ·
      refine ⟨23692490297305063079950579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31589987063073417439934105 23692490297305063079950579)
      ·
        refine ⟨35538735445957594619925869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23692490297305063079950579 35538735445957594619925869)
        ·
          refine ⟨13327025792234097982472201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35538735445957594619925869 13327025792234097982472201)
          ·
            refine ⟨9995269344175573486854151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13327025792234097982472201 9995269344175573486854151)
            ·
              refine ⟨14992904016263360230281227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9995269344175573486854151 14992904016263360230281227)
              ·
                refine ⟨22489356024395040345421841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14992904016263360230281227 22489356024395040345421841)
                ·
                  refine ⟨16867017018296280259066381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22489356024395040345421841 16867017018296280259066381)
                  ·
                    refine ⟨6325131381861105097149893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16867017018296280259066381 6325131381861105097149893)
                    ·
                      refine ⟨1185962134098957205715605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6325131381861105097149893 1185962134098957205715605)
                      ·
                        rfl

theorem cell23_2309653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_2309653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309653 prefixEnd_2309653 := by exact prefixLift 2309653
  have htrace : WordTrace (prefixWord ++ tailWord_2309653) baseStart_2309653 baseEnd_2309653 := by
    simpa [prefixWord, tailWord_2309653, baseEnd_2309653] using wordTrace_append hprefix tailTrace_2309653
  have hstable : (prefixWord ++ tailWord_2309653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309653).length < 2 ^ (prefixWord ++ tailWord_2309653).sum := by decide
  have hdescent : baseEnd_2309653 < baseStart_2309653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309760 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_2309760 : Nat := 118140960795 + 2309760 * 2 ^ 59
def prefixEnd_2309760 : Nat := 4983230072969 + 3 ^ 40 * 2309760 * 2
def baseEnd_2309760 : Nat := 1186017076528988287077613

theorem tailTrace_2309760 : CollatzResearch.WordTrace tailWord_2309760 prefixEnd_2309760 1186017076528988287077613 := by
  unfold tailWord_2309760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42121934056070735223651367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56162578741427646964868489 42121934056070735223651367)
  ·
    refine ⟨63182901084106102835477051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42121934056070735223651367 63182901084106102835477051)
    ·
      refine ⟨94774351626159154253215577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63182901084106102835477051 94774351626159154253215577)
      ·
        refine ⟨71080763719619365689911683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94774351626159154253215577 71080763719619365689911683)
        ·
          refine ⟨106621145579429048534867525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71080763719619365689911683 106621145579429048534867525)
          ·
            refine ⟨19991464796142946600287661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106621145579429048534867525 19991464796142946600287661)
            ·
              refine ⟨7496799298553604975107873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19991464796142946600287661 7496799298553604975107873)
              ·
                refine ⟨5622599473915203731330905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7496799298553604975107873 5622599473915203731330905)
                ·
                  refine ⟨4216949605436402798498179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5622599473915203731330905 4216949605436402798498179)
                  ·
                    refine ⟨6325424408154604197747269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4216949605436402798498179 6325424408154604197747269)
                    ·
                      refine ⟨1186017076528988287077613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6325424408154604197747269 1186017076528988287077613)
                      ·
                        rfl

theorem cell23_2309760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_2309760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309760 prefixEnd_2309760 := by exact prefixLift 2309760
  have htrace : WordTrace (prefixWord ++ tailWord_2309760) baseStart_2309760 baseEnd_2309760 := by
    simpa [prefixWord, tailWord_2309760, baseEnd_2309760] using wordTrace_append hprefix tailTrace_2309760
  have hstable : (prefixWord ++ tailWord_2309760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309760).length < 2 ^ (prefixWord ++ tailWord_2309760).sum := by decide
  have hdescent : baseEnd_2309760 < baseStart_2309760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309844 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2309844 : Nat := 118140960795 + 2309844 * 2 ^ 59
def prefixEnd_2309844 : Nat := 4983230072969 + 3 ^ 40 * 2309844 * 2
def baseEnd_2309844 : Nat := 1186060208903965958427227

theorem tailTrace_2309844 : CollatzResearch.WordTrace tailWord_2309844 prefixEnd_2309844 1186060208903965958427227 := by
  unfold tailWord_2309844
  simp only [CollatzResearch.WordTrace]
  refine ⟨42123465921918576396680293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56164621229224768528907057 42123465921918576396680293)
  ·
    refine ⟨7898149860359733074377555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42123465921918576396680293 7898149860359733074377555)
    ·
      refine ⟨11847224790539599611566333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7898149860359733074377555 11847224790539599611566333)
      ·
        refine ⟨4442709296452349854337375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11847224790539599611566333 4442709296452349854337375)
        ·
          refine ⟨6664063944678524781506063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4442709296452349854337375 6664063944678524781506063)
          ·
            refine ⟨9996095917017787172259095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6664063944678524781506063 9996095917017787172259095)
            ·
              refine ⟨14994143875526680758388643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9996095917017787172259095 14994143875526680758388643)
              ·
                refine ⟨22491215813290021137582965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14994143875526680758388643 22491215813290021137582965)
                ·
                  refine ⟨2108551482495939481648403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22491215813290021137582965 2108551482495939481648403)
                  ·
                    refine ⟨3162827223743909222472605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2108551482495939481648403 3162827223743909222472605)
                    ·
                      refine ⟨1186060208903965958427227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3162827223743909222472605 1186060208903965958427227)
                      ·
                        rfl

theorem cell23_2309844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2309844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309844 prefixEnd_2309844 := by exact prefixLift 2309844
  have htrace : WordTrace (prefixWord ++ tailWord_2309844) baseStart_2309844 baseEnd_2309844 := by
    simpa [prefixWord, tailWord_2309844, baseEnd_2309844] using wordTrace_append hprefix tailTrace_2309844
  have hstable : (prefixWord ++ tailWord_2309844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309844).length < 2 ^ (prefixWord ++ tailWord_2309844).sum := by decide
  have hdescent : baseEnd_2309844 < baseStart_2309844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309860 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_2309860 : Nat := 118140960795 + 2309860 * 2 ^ 59
def prefixEnd_2309860 : Nat := 4983230072969 + 3 ^ 40 * 2309860 * 2
def baseEnd_2309860 : Nat := 395356141531479298609051

theorem tailTrace_2309860 : CollatzResearch.WordTrace tailWord_2309860 prefixEnd_2309860 395356141531479298609051 := by
  unfold tailWord_2309860
  simp only [CollatzResearch.WordTrace]
  refine ⟨42123757705889593762971517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56165010274519458350628689 42123757705889593762971517)
  ·
    refine ⟨15796409139708597661114319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42123757705889593762971517 15796409139708597661114319)
    ·
      refine ⟨23694613709562896491671479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15796409139708597661114319 23694613709562896491671479)
      ·
        refine ⟨35541920564344344737507219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23694613709562896491671479 35541920564344344737507219)
        ·
          refine ⟨53312880846516517106260829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35541920564344344737507219 53312880846516517106260829)
          ·
            refine ⟨19992330317443693914847811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53312880846516517106260829 19992330317443693914847811)
            ·
              refine ⟨29988495476165540872271717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19992330317443693914847811 29988495476165540872271717)
              ·
                refine ⟨5622842901781038913550947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29988495476165540872271717 5622842901781038913550947)
                ·
                  refine ⟨8434264352671558370326421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5622842901781038913550947 8434264352671558370326421)
                  ·
                    refine ⟨395356141531479298609051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8434264352671558370326421 395356141531479298609051)
                    ·
                      rfl

theorem cell23_2309860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_2309860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309860 prefixEnd_2309860 := by exact prefixLift 2309860
  have htrace : WordTrace (prefixWord ++ tailWord_2309860) baseStart_2309860 baseEnd_2309860 := by
    simpa [prefixWord, tailWord_2309860, baseEnd_2309860] using wordTrace_append hprefix tailTrace_2309860
  have hstable : (prefixWord ++ tailWord_2309860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309860).length < 2 ^ (prefixWord ++ tailWord_2309860).sum := by decide
  have hdescent : baseEnd_2309860 < baseStart_2309860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309861 : List Nat := [1, 3, 1, 4, 1, 1, 4, 3, 1, 1, 3]
def baseStart_2309861 : Nat := 118140960795 + 2309861 * 2 ^ 59
def prefixEnd_2309861 : Nat := 4983230072969 + 3 ^ 40 * 2309861 * 2
def baseEnd_2309861 : Nat := 1186068938075092391914649

theorem tailTrace_2309861 : CollatzResearch.WordTrace tailWord_2309861 prefixEnd_2309861 1186068938075092391914649 := by
  unfold tailWord_2309861
  simp only [CollatzResearch.WordTrace]
  refine ⟨84247551884775564696729437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56165034589850376464486291 84247551884775564696729437)
  ·
    refine ⟨31592831956790836761273539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84247551884775564696729437 31592831956790836761273539)
    ·
      refine ⟨47389247935186255141910309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31592831956790836761273539 47389247935186255141910309)
      ·
        refine ⟨8885483987847422839108183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47389247935186255141910309 8885483987847422839108183)
        ·
          refine ⟨13328225981771134258662275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8885483987847422839108183 13328225981771134258662275)
          ·
            refine ⟨19992338972656701387993413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13328225981771134258662275 19992338972656701387993413)
            ·
              refine ⟨3748563557373131510248765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19992338972656701387993413 3748563557373131510248765)
              ·
                refine ⟨1405711334014924316343287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3748563557373131510248765 1405711334014924316343287)
                ·
                  refine ⟨2108567001022386474514931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405711334014924316343287 2108567001022386474514931)
                  ·
                    refine ⟨3162850501533579711772397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2108567001022386474514931 3162850501533579711772397)
                    ·
                      refine ⟨1186068938075092391914649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3162850501533579711772397 1186068938075092391914649)
                      ·
                        rfl

theorem cell23_2309861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_2309861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309861 prefixEnd_2309861 := by exact prefixLift 2309861
  have htrace : WordTrace (prefixWord ++ tailWord_2309861) baseStart_2309861 baseEnd_2309861 := by
    simpa [prefixWord, tailWord_2309861, baseEnd_2309861] using wordTrace_append hprefix tailTrace_2309861
  have hstable : (prefixWord ++ tailWord_2309861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309861).length < 2 ^ (prefixWord ++ tailWord_2309861).sum := by decide
  have hdescent : baseEnd_2309861 < baseStart_2309861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309864 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 1, 5]
def baseStart_2309864 : Nat := 118140960795 + 2309864 * 2 ^ 59
def prefixEnd_2309864 : Nat := 4983230072969 + 3 ^ 40 * 2309864 * 2
def baseEnd_2309864 : Nat := 395356826172351960059045

theorem tailTrace_2309864 : CollatzResearch.WordTrace tailWord_2309864 prefixEnd_2309864 395356826172351960059045 := by
  unfold tailWord_2309864
  simp only [CollatzResearch.WordTrace]
  refine ⟨42123830651882348104544323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56165107535843130806059097 42123830651882348104544323)
  ·
    refine ⟨63185745977823522156816485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42123830651882348104544323 63185745977823522156816485)
    ·
      refine ⟨11847327370841910404403091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63185745977823522156816485 11847327370841910404403091)
      ·
        refine ⟨17770991056262865606604637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11847327370841910404403091 17770991056262865606604637)
        ·
          refine ⟨6664121646098574602476739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17770991056262865606604637 6664121646098574602476739)
          ·
            refine ⟨9996182469147861903715109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6664121646098574602476739 9996182469147861903715109)
            ·
              refine ⟨1874284212965224106946583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9996182469147861903715109 1874284212965224106946583)
              ·
                refine ⟨2811426319447836160419875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874284212965224106946583 2811426319447836160419875)
                ·
                  refine ⟨4217139479171754240629813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811426319447836160419875 4217139479171754240629813)
                  ·
                    refine ⟨395356826172351960059045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4217139479171754240629813 395356826172351960059045)
                    ·
                      rfl

theorem cell23_2309864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_2309864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309864 prefixEnd_2309864 := by exact prefixLift 2309864
  have htrace : WordTrace (prefixWord ++ tailWord_2309864) baseStart_2309864 baseEnd_2309864 := by
    simpa [prefixWord, tailWord_2309864, baseEnd_2309864] using wordTrace_append hprefix tailTrace_2309864
  have hstable : (prefixWord ++ tailWord_2309864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309864).length < 2 ^ (prefixWord ++ tailWord_2309864).sum := by decide
  have hdescent : baseEnd_2309864 < baseStart_2309864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309945 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 2, 4]
def baseStart_2309945 : Nat := 118140960795 + 2309945 * 2 ^ 59
def prefixEnd_2309945 : Nat := 4983230072969 + 3 ^ 40 * 2309945 * 2
def baseEnd_2309945 : Nat := 395370690150023354421421

theorem tailTrace_2309945 : CollatzResearch.WordTrace tailWord_2309945 prefixEnd_2309945 395370690150023354421421 := by
  unfold tailWord_2309945
  simp only [CollatzResearch.WordTrace]
  refine ⟨84250615616471247042787289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56167077077647498028524859 84250615616471247042787289)
  ·
    refine ⟨63187961712353435282090467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84250615616471247042787289 63187961712353435282090467)
    ·
      refine ⟨94781942568530152923135701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63187961712353435282090467 94781942568530152923135701)
      ·
        refine ⟨2221451778949925459135993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 94781942568530152923135701 2221451778949925459135993)
        ·
          refine ⟨1666088834212444094351995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2221451778949925459135993 1666088834212444094351995)
          ·
            refine ⟨2499133251318666141527993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666088834212444094351995 2499133251318666141527993)
            ·
              refine ⟨1874349938488999606145995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2499133251318666141527993 1874349938488999606145995)
              ·
                refine ⟨2811524907733499409218993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874349938488999606145995 2811524907733499409218993)
                ·
                  refine ⟨2108643680800124556914245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2811524907733499409218993 2108643680800124556914245)
                  ·
                    refine ⟨395370690150023354421421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2108643680800124556914245 395370690150023354421421)
                    ·
                      rfl

theorem cell23_2309945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 4].length) (baseStart_2309945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309945 prefixEnd_2309945 := by exact prefixLift 2309945
  have htrace : WordTrace (prefixWord ++ tailWord_2309945) baseStart_2309945 baseEnd_2309945 := by
    simpa [prefixWord, tailWord_2309945, baseEnd_2309945] using wordTrace_append hprefix tailTrace_2309945
  have hstable : (prefixWord ++ tailWord_2309945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309945).length < 2 ^ (prefixWord ++ tailWord_2309945).sum := by decide
  have hdescent : baseEnd_2309945 < baseStart_2309945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309951 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 3]
def baseStart_2309951 : Nat := 118140960795 + 2309951 * 2 ^ 59
def prefixEnd_2309951 : Nat := 4983230072969 + 3 ^ 40 * 2309951 * 2
def baseEnd_2309951 : Nat := 1186115151333997039789235

theorem tailTrace_2309951 : CollatzResearch.WordTrace tailWord_2309951 prefixEnd_2309951 1186115151333997039789235 := by
  unfold tailWord_2309951
  simp only [CollatzResearch.WordTrace]
  refine ⟨84250834454449510067505707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56167222969633006711670471 84250834454449510067505707)
  ·
    refine ⟨126376251681674265101258561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84250834454449510067505707 126376251681674265101258561)
    ·
      refine ⟨94782188761255698825943921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126376251681674265101258561 94782188761255698825943921)
      ·
        refine ⟨71086641570941774119457941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94782188761255698825943921 71086641570941774119457941)
        ·
          refine ⟨3332186323637895661849591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71086641570941774119457941 3332186323637895661849591)
          ·
            refine ⟨4998279485456843492774387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332186323637895661849591 4998279485456843492774387)
            ·
              refine ⟨7497419228185265239161581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4998279485456843492774387 7497419228185265239161581)
              ·
                refine ⟨2811532210569474464685593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7497419228185265239161581 2811532210569474464685593)
                ·
                  refine ⟨2108649157927105848514195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2811532210569474464685593 2108649157927105848514195)
                  ·
                    refine ⟨3162973736890658772771293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2108649157927105848514195 3162973736890658772771293)
                    ·
                      refine ⟨1186115151333997039789235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3162973736890658772771293 1186115151333997039789235)
                      ·
                        rfl

theorem cell23_2309951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_2309951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2309951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2309951 prefixEnd_2309951 := by exact prefixLift 2309951
  have htrace : WordTrace (prefixWord ++ tailWord_2309951) baseStart_2309951 baseEnd_2309951 := by
    simpa [prefixWord, tailWord_2309951, baseEnd_2309951] using wordTrace_append hprefix tailTrace_2309951
  have hstable : (prefixWord ++ tailWord_2309951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309951).length < 2 ^ (prefixWord ++ tailWord_2309951).sum := by decide
  have hdescent : baseEnd_2309951 < baseStart_2309951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310000 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_2310000 : Nat := 118140960795 + 2310000 * 2 ^ 59
def prefixEnd_2310000 : Nat := 4983230072969 + 3 ^ 40 * 2310000 * 2
def baseEnd_2310000 : Nat := 1186140311886067348076509

theorem tailTrace_2310000 : CollatzResearch.WordTrace tailWord_2310000 prefixEnd_2310000 1186140311886067348076509 := by
  unfold tailWord_2310000
  simp only [CollatzResearch.WordTrace]
  refine ⟨42126310815635995718019727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56168414420847994290692969 42126310815635995718019727)
  ·
    refine ⟨63189466223453993577029591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42126310815635995718019727 63189466223453993577029591)
    ·
      refine ⟨94784199335180990365544387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63189466223453993577029591 94784199335180990365544387)
      ·
        refine ⟨142176299002771485548316581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94784199335180990365544387 142176299002771485548316581)
        ·
          refine ⟨26658056063019653540309359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142176299002771485548316581 26658056063019653540309359)
          ·
            refine ⟨39987084094529480310464039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26658056063019653540309359 39987084094529480310464039)
            ·
              refine ⟨59980626141794220465696059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39987084094529480310464039 59980626141794220465696059)
              ·
                refine ⟨89970939212691330698544089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59980626141794220465696059 89970939212691330698544089)
                ·
                  refine ⟨67478204409518498023908067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89970939212691330698544089 67478204409518498023908067)
                  ·
                    refine ⟨101217306614277747035862101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67478204409518498023908067 101217306614277747035862101)
                    ·
                      refine ⟨1186140311886067348076509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 101217306614277747035862101 1186140311886067348076509)
                      ·
                        rfl

theorem cell23_2310000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_2310000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310000 prefixEnd_2310000 := by exact prefixLift 2310000
  have htrace : WordTrace (prefixWord ++ tailWord_2310000) baseStart_2310000 baseEnd_2310000 := by
    simpa [prefixWord, tailWord_2310000, baseEnd_2310000] using wordTrace_append hprefix tailTrace_2310000
  have hstable : (prefixWord ++ tailWord_2310000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310000).length < 2 ^ (prefixWord ++ tailWord_2310000).sum := by decide
  have hdescent : baseEnd_2310000 < baseStart_2310000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310014 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_2310014 : Nat := 118140960795 + 2310014 * 2 ^ 59
def prefixEnd_2310014 : Nat := 4983230072969 + 3 ^ 40 * 2310014 * 2
def baseEnd_2310014 : Nat := 131794166735025588144605

theorem tailTrace_2310014 : CollatzResearch.WordTrace tailWord_2310014 prefixEnd_2310014 131794166735025588144605 := by
  unfold tailWord_2310014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10531641531652658978381137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56168754835480847884699397 10531641531652658978381137)
  ·
    refine ⟨7898731148739494233785853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10531641531652658978381137 7898731148739494233785853)
    ·
      refine ⟨2962024180777310337669695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7898731148739494233785853 2962024180777310337669695)
      ·
        refine ⟨4443036271165965506504543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962024180777310337669695 4443036271165965506504543)
        ·
          refine ⟨6664554406748948259756815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4443036271165965506504543 6664554406748948259756815)
          ·
            refine ⟨9996831610123422389635223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6664554406748948259756815 9996831610123422389635223)
            ·
              refine ⟨14995247415185133584452835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9996831610123422389635223 14995247415185133584452835)
              ·
                refine ⟨22492871122777700376679253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14995247415185133584452835 22492871122777700376679253)
                ·
                  refine ⟨131794166735025588144605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22492871122777700376679253 131794166735025588144605)
                  ·
                    rfl

theorem cell23_2310014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_2310014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310014 prefixEnd_2310014 := by exact prefixLift 2310014
  have htrace : WordTrace (prefixWord ++ tailWord_2310014) baseStart_2310014 baseEnd_2310014 := by
    simpa [prefixWord, tailWord_2310014, baseEnd_2310014] using wordTrace_append hprefix tailTrace_2310014
  have hstable : (prefixWord ++ tailWord_2310014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310014).length < 2 ^ (prefixWord ++ tailWord_2310014).sum := by decide
  have hdescent : baseEnd_2310014 < baseStart_2310014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310067 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 3]
def baseStart_2310067 : Nat := 118140960795 + 2310067 * 2 ^ 59
def prefixEnd_2310067 : Nat := 4983230072969 + 3 ^ 40 * 2310067 * 2
def baseEnd_2310067 : Nat := 1186174715089918585938701

theorem tailTrace_2310067 : CollatzResearch.WordTrace tailWord_2310067 prefixEnd_2310067 1186174715089918585938701 := by
  unfold tailWord_2310067
  simp only [CollatzResearch.WordTrace]
  refine ⟨84255065322029261878728455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56170043548019507919152303 84255065322029261878728455)
  ·
    refine ⟨126382597983043892818092683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84255065322029261878728455 126382597983043892818092683)
    ·
      refine ⟨189573896974565839227139025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126382597983043892818092683 189573896974565839227139025)
      ·
        refine ⟨142180422730924379420354269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189573896974565839227139025 142180422730924379420354269)
        ·
          refine ⟨53317658524096642282632851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142180422730924379420354269 53317658524096642282632851)
          ·
            refine ⟨79976487786144963423949277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53317658524096642282632851 79976487786144963423949277)
            ·
              refine ⟨29991182919804361283980979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79976487786144963423949277 29991182919804361283980979)
              ·
                refine ⟨44986774379706541925971469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29991182919804361283980979 44986774379706541925971469)
                ·
                  refine ⟨16870040392389953222239301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44986774379706541925971469 16870040392389953222239301)
                  ·
                    refine ⟨3163132573573116229169869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16870040392389953222239301 3163132573573116229169869)
                    ·
                      refine ⟨1186174715089918585938701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3163132573573116229169869 1186174715089918585938701)
                      ·
                        rfl

theorem cell23_2310067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_2310067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310067 prefixEnd_2310067 := by exact prefixLift 2310067
  have htrace : WordTrace (prefixWord ++ tailWord_2310067) baseStart_2310067 baseEnd_2310067 := by
    simpa [prefixWord, tailWord_2310067, baseEnd_2310067] using wordTrace_append hprefix tailTrace_2310067
  have hstable : (prefixWord ++ tailWord_2310067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310067).length < 2 ^ (prefixWord ++ tailWord_2310067).sum := by decide
  have hdescent : baseEnd_2310067 < baseStart_2310067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310101 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2310101 : Nat := 118140960795 + 2310101 * 2 ^ 59
def prefixEnd_2310101 : Nat := 4983230072969 + 3 ^ 40 * 2310101 * 2
def baseEnd_2310101 : Nat := 1186192173432171452913545

theorem tailTrace_2310101 : CollatzResearch.WordTrace tailWord_2310101 prefixEnd_2310101 1186192173432171452913545 := by
  unfold tailWord_2310101
  simp only [CollatzResearch.WordTrace]
  refine ⟨84256305403906085685466157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56170870269270723790310771 84256305403906085685466157)
  ·
    refine ⟨31596114526464782132049809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84256305403906085685466157 31596114526464782132049809)
    ·
      refine ⟨23697085894848586599037357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31596114526464782132049809 23697085894848586599037357)
      ·
        refine ⟨8886407210568219974639009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23697085894848586599037357 8886407210568219974639009)
        ·
          refine ⟨6664805407926164980979257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8886407210568219974639009 6664805407926164980979257)
          ·
            refine ⟨4998604055944623735734443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6664805407926164980979257 4998604055944623735734443)
            ·
              refine ⟨7497906083916935603601665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4998604055944623735734443 7497906083916935603601665)
              ·
                refine ⟨5623429562937701702701249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7497906083916935603601665 5623429562937701702701249)
                ·
                  refine ⟨4217572172203276277025937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5623429562937701702701249 4217572172203276277025937)
                  ·
                    refine ⟨3163179129152457207769453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4217572172203276277025937 3163179129152457207769453)
                    ·
                      refine ⟨1186192173432171452913545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3163179129152457207769453 1186192173432171452913545)
                      ·
                        rfl

theorem cell23_2310101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2310101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310101 prefixEnd_2310101 := by exact prefixLift 2310101
  have htrace : WordTrace (prefixWord ++ tailWord_2310101) baseStart_2310101 baseEnd_2310101 := by
    simpa [prefixWord, tailWord_2310101, baseEnd_2310101] using wordTrace_append hprefix tailTrace_2310101
  have hstable : (prefixWord ++ tailWord_2310101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310101).length < 2 ^ (prefixWord ++ tailWord_2310101).sum := by decide
  have hdescent : baseEnd_2310101 < baseStart_2310101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310124 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 3, 5, 2]
def baseStart_2310124 : Nat := 118140960795 + 2310124 * 2 ^ 59
def prefixEnd_2310124 : Nat := 4983230072969 + 3 ^ 40 * 2310124 * 2
def baseEnd_2310124 : Nat := 1186203983487224862925939

theorem tailTrace_2310124 : CollatzResearch.WordTrace tailWord_2310124 prefixEnd_2310124 1186203983487224862925939 := by
  unfold tailWord_2310124
  simp only [CollatzResearch.WordTrace]
  refine ⟨42128572141411380306776713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56171429521881840409035617 42128572141411380306776713)
  ·
    refine ⟨31596429106058535230082535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42128572141411380306776713 31596429106058535230082535)
    ·
      refine ⟨47394643659087802845123803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31596429106058535230082535 47394643659087802845123803)
      ·
        refine ⟨71091965488631704267685705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47394643659087802845123803 71091965488631704267685705)
        ·
          refine ⟨53318974116473778200764279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71091965488631704267685705 53318974116473778200764279)
          ·
            refine ⟨79978461174710667301146419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53318974116473778200764279 79978461174710667301146419)
            ·
              refine ⟨119967691762066000951719629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79978461174710667301146419 119967691762066000951719629)
              ·
                refine ⟨44987884410774750356894861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119967691762066000951719629 44987884410774750356894861)
                ·
                  refine ⟨16870456654040531383835573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44987884410774750356894861 16870456654040531383835573)
                  ·
                    refine ⟨1581605311316299817234585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16870456654040531383835573 1581605311316299817234585)
                    ·
                      refine ⟨1186203983487224862925939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1581605311316299817234585 1186203983487224862925939)
                      ·
                        rfl

theorem cell23_2310124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_2310124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310124 prefixEnd_2310124 := by exact prefixLift 2310124
  have htrace : WordTrace (prefixWord ++ tailWord_2310124) baseStart_2310124 baseEnd_2310124 := by
    simpa [prefixWord, tailWord_2310124, baseEnd_2310124] using wordTrace_append hprefix tailTrace_2310124
  have hstable : (prefixWord ++ tailWord_2310124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310124).length < 2 ^ (prefixWord ++ tailWord_2310124).sum := by decide
  have hdescent : baseEnd_2310124 < baseStart_2310124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310141 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_2310141 : Nat := 118140960795 + 2310141 * 2 ^ 59
def prefixEnd_2310141 : Nat := 4983230072969 + 3 ^ 40 * 2310141 * 2
def baseEnd_2310141 : Nat := 1186212712658351296413361

theorem tailTrace_2310141 : CollatzResearch.WordTrace tailWord_2310141 prefixEnd_2310141 1186212712658351296413361 := by
  unfold tailWord_2310141
  simp only [CollatzResearch.WordTrace]
  refine ⟨84257764323761172516922277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56171842882507448344614851 84257764323761172516922277)
  ·
    refine ⟨15798330810705219846922927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84257764323761172516922277 15798330810705219846922927)
    ·
      refine ⟨23697496216057829770384391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15798330810705219846922927 23697496216057829770384391)
      ·
        refine ⟨35546244324086744655576587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23697496216057829770384391 35546244324086744655576587)
        ·
          refine ⟨53319366486130116983364881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35546244324086744655576587 53319366486130116983364881)
          ·
            refine ⟨39989524864597587737523661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53319366486130116983364881 39989524864597587737523661)
            ·
              refine ⟨14996071824224095401571373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39989524864597587737523661 14996071824224095401571373)
              ·
                refine ⟨5623526934084035775589265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14996071824224095401571373 5623526934084035775589265)
                ·
                  refine ⟨4217645200563026831691949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5623526934084035775589265 4217645200563026831691949)
                  ·
                    refine ⟨1581616950211135061884481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4217645200563026831691949 1581616950211135061884481)
                    ·
                      refine ⟨1186212712658351296413361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1581616950211135061884481 1186212712658351296413361)
                      ·
                        rfl

theorem cell23_2310141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_2310141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310141 prefixEnd_2310141 := by exact prefixLift 2310141
  have htrace : WordTrace (prefixWord ++ tailWord_2310141) baseStart_2310141 baseEnd_2310141 := by
    simpa [prefixWord, tailWord_2310141, baseEnd_2310141] using wordTrace_append hprefix tailTrace_2310141
  have hstable : (prefixWord ++ tailWord_2310141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310141).length < 2 ^ (prefixWord ++ tailWord_2310141).sum := by decide
  have hdescent : baseEnd_2310141 < baseStart_2310141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310165 : List Nat := [1, 3, 2, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_2310165 : Nat := 118140960795 + 2310165 * 2 ^ 59
def prefixEnd_2310165 : Nat := 4983230072969 + 3 ^ 40 * 2310165 * 2
def baseEnd_2310165 : Nat := 1186225036194059202513251

theorem tailTrace_2310165 : CollatzResearch.WordTrace tailWord_2310165 prefixEnd_2310165 1186225036194059202513251 := by
  unfold tailWord_2310165
  simp only [CollatzResearch.WordTrace]
  refine ⟨84258639675674224615795949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56172426450449483077197299 84258639675674224615795949)
  ·
    refine ⟨31596989878377834230923481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84258639675674224615795949 31596989878377834230923481)
    ·
      refine ⟨23697742408783375673192611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31596989878377834230923481 23697742408783375673192611)
      ·
        refine ⟨35546613613175063509788917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23697742408783375673192611 35546613613175063509788917)
        ·
          refine ⟨3332495026235162204042711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35546613613175063509788917 3332495026235162204042711)
          ·
            refine ⟨4998742539352743306064067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332495026235162204042711 4998742539352743306064067)
            ·
              refine ⟨7498113809029114959096101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4998742539352743306064067 7498113809029114959096101)
              ·
                refine ⟨1405896339192959054830519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7498113809029114959096101 1405896339192959054830519)
                ·
                  refine ⟨2108844508789438582245779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405896339192959054830519 2108844508789438582245779)
                  ·
                    refine ⟨3163266763184157873368669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2108844508789438582245779 3163266763184157873368669)
                    ·
                      refine ⟨1186225036194059202513251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3163266763184157873368669 1186225036194059202513251)
                      ·
                        rfl

theorem cell23_2310165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_2310165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310165 prefixEnd_2310165 := by exact prefixLift 2310165
  have htrace : WordTrace (prefixWord ++ tailWord_2310165) baseStart_2310165 baseEnd_2310165 := by
    simpa [prefixWord, tailWord_2310165, baseEnd_2310165] using wordTrace_append hprefix tailTrace_2310165
  have hstable : (prefixWord ++ tailWord_2310165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310165).length < 2 ^ (prefixWord ++ tailWord_2310165).sum := by decide
  have hdescent : baseEnd_2310165 < baseStart_2310165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310181 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_2310181 : Nat := 118140960795 + 2310181 * 2 ^ 59
def prefixEnd_2310181 : Nat := 4983230072969 + 3 ^ 40 * 2310181 * 2
def baseEnd_2310181 : Nat := 395411083961510379971059

theorem tailTrace_2310181 : CollatzResearch.WordTrace tailWord_2310181 prefixEnd_2310181 395411083961510379971059 := by
  unfold tailWord_2310181
  simp only [CollatzResearch.WordTrace]
  refine ⟨84259223243616259348378397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56172815495744172898918931 84259223243616259348378397)
  ·
    refine ⟨31597208716356097255641899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84259223243616259348378397 31597208716356097255641899)
    ·
      refine ⟨47395813074534145883462849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31597208716356097255641899 47395813074534145883462849)
      ·
        refine ⟨35546859805900609412597137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47395813074534145883462849 35546859805900609412597137)
        ·
          refine ⟨26660144854425457059447853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35546859805900609412597137 26660144854425457059447853)
          ·
            refine ⟨9997554320409546397292945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26660144854425457059447853 9997554320409546397292945)
            ·
              refine ⟨7498165740307159797969709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9997554320409546397292945 7498165740307159797969709)
              ·
                refine ⟨2811812152615184924238641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7498165740307159797969709 2811812152615184924238641)
                ·
                  refine ⟨2108859114461388693178981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2811812152615184924238641 2108859114461388693178981)
                  ·
                    refine ⟨395411083961510379971059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2108859114461388693178981 395411083961510379971059)
                    ·
                      rfl

theorem cell23_2310181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_2310181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310181 prefixEnd_2310181 := by exact prefixLift 2310181
  have htrace : WordTrace (prefixWord ++ tailWord_2310181) baseStart_2310181 baseEnd_2310181 := by
    simpa [prefixWord, tailWord_2310181, baseEnd_2310181] using wordTrace_append hprefix tailTrace_2310181
  have hstable : (prefixWord ++ tailWord_2310181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310181).length < 2 ^ (prefixWord ++ tailWord_2310181).sum := by decide
  have hdescent : baseEnd_2310181 < baseStart_2310181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310208 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 1, 2, 3]
def baseStart_2310208 : Nat := 118140960795 + 2310208 * 2 ^ 59
def prefixEnd_2310208 : Nat := 4983230072969 + 3 ^ 40 * 2310208 * 2
def baseEnd_2310208 : Nat := 1186247115862202534275553

theorem tailTrace_2310208 : CollatzResearch.WordTrace tailWord_2310208 prefixEnd_2310208 1186247115862202534275553 := by
  unfold tailWord_2310208
  simp only [CollatzResearch.WordTrace]
  refine ⟨42130104007259221479805639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56173472009678961973074185 42130104007259221479805639)
  ·
    refine ⟨63195156010888832219708459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42130104007259221479805639 63195156010888832219708459)
    ·
      refine ⟨94792734016333248329562689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63195156010888832219708459 94792734016333248329562689)
      ·
        refine ⟨71094550512249936247172017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94792734016333248329562689 71094550512249936247172017)
        ·
          refine ⟨53320912884187452185379013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71094550512249936247172017 53320912884187452185379013)
          ·
            refine ⟨9997671165785147284758565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53320912884187452185379013 9997671165785147284758565)
            ·
              refine ⟨1874563343584715115892231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9997671165785147284758565 1874563343584715115892231)
              ·
                refine ⟨2811845015377072673838347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874563343584715115892231 2811845015377072673838347)
                ·
                  refine ⟨4217767523065609010757521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811845015377072673838347 4217767523065609010757521)
                  ·
                    refine ⟨3163325642299206758068141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4217767523065609010757521 3163325642299206758068141)
                    ·
                      refine ⟨1186247115862202534275553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3163325642299206758068141 1186247115862202534275553)
                      ·
                        rfl

theorem cell23_2310208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_2310208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310208 prefixEnd_2310208 := by exact prefixLift 2310208
  have htrace : WordTrace (prefixWord ++ tailWord_2310208) baseStart_2310208 baseEnd_2310208 := by
    simpa [prefixWord, tailWord_2310208, baseEnd_2310208] using wordTrace_append hprefix tailTrace_2310208
  have hstable : (prefixWord ++ tailWord_2310208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310208).length < 2 ^ (prefixWord ++ tailWord_2310208).sum := by decide
  have hdescent : baseEnd_2310208 < baseStart_2310208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310227 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 10]
def baseStart_2310227 : Nat := 118140960795 + 2310227 * 2 ^ 59
def prefixEnd_2310227 : Nat := 4983230072969 + 3 ^ 40 * 2310227 * 2
def baseEnd_2310227 : Nat := 1186256871994637959937965

theorem tailTrace_2310227 : CollatzResearch.WordTrace tailWord_2310227 prefixEnd_2310227 1186256871994637959937965 := by
  unfold tailWord_2310227
  simp only [CollatzResearch.WordTrace]
  refine ⟨84260901001449609204552935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56173934000966406136368623 84260901001449609204552935)
  ·
    refine ⟨126391351502174413806829403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84260901001449609204552935 126391351502174413806829403)
    ·
      refine ⟨189587027253261620710244105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126391351502174413806829403 189587027253261620710244105)
      ·
        refine ⟨142190270439946215532683079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189587027253261620710244105 142190270439946215532683079)
        ·
          refine ⟨213285405659919323299024619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142190270439946215532683079 213285405659919323299024619)
          ·
            refine ⟨319928108489878984948536929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213285405659919323299024619 319928108489878984948536929)
            ·
              refine ⟨239946081367409238711402697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319928108489878984948536929 239946081367409238711402697)
              ·
                refine ⟨179959561025556929033552023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239946081367409238711402697 179959561025556929033552023)
                ·
                  refine ⟨269939341538335393550328035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179959561025556929033552023 269939341538335393550328035)
                  ·
                    refine ⟨404909012307503090325492053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 269939341538335393550328035 404909012307503090325492053)
                    ·
                      refine ⟨1186256871994637959937965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 404909012307503090325492053 1186256871994637959937965)
                      ·
                        rfl

theorem cell23_2310227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_2310227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310227 prefixEnd_2310227 := by exact prefixLift 2310227
  have htrace : WordTrace (prefixWord ++ tailWord_2310227) baseStart_2310227 baseEnd_2310227 := by
    simpa [prefixWord, tailWord_2310227, baseEnd_2310227] using wordTrace_append hprefix tailTrace_2310227
  have hstable : (prefixWord ++ tailWord_2310227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310227).length < 2 ^ (prefixWord ++ tailWord_2310227).sum := by decide
  have hdescent : baseEnd_2310227 < baseStart_2310227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310231 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 5, 3, 2]
def baseStart_2310231 : Nat := 118140960795 + 2310231 * 2 ^ 59
def prefixEnd_2310231 : Nat := 4983230072969 + 3 ^ 40 * 2310231 * 2
def baseEnd_2310231 : Nat := 1186258925917255944287947

theorem tailTrace_2310231 : CollatzResearch.WordTrace tailWord_2310231 prefixEnd_2310231 1186258925917255944287947 := by
  unfold tailWord_2310231
  simp only [CollatzResearch.WordTrace]
  refine ⟨84261046893435117887698547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56174031262290078591799031 84261046893435117887698547)
  ·
    refine ⟨126391570340152676831547821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84261046893435117887698547 126391570340152676831547821)
    ·
      refine ⟨47396838877557253811830433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126391570340152676831547821 47396838877557253811830433)
      ·
        refine ⟨35547629158167940358872825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47396838877557253811830433 35547629158167940358872825)
        ·
          refine ⟨26660721868625955269154619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35547629158167940358872825 26660721868625955269154619)
          ·
            refine ⟨39991082802938932903731929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26660721868625955269154619 39991082802938932903731929)
            ·
              refine ⟨29993312102204199677798947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39991082802938932903731929 29993312102204199677798947)
              ·
                refine ⟨44989968153306299516698421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29993312102204199677798947 44989968153306299516698421)
                ·
                  refine ⟨4217809514372465579690477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44989968153306299516698421 4217809514372465579690477)
                  ·
                    refine ⟨1581678567889674592383929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4217809514372465579690477 1581678567889674592383929)
                    ·
                      refine ⟨1186258925917255944287947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1581678567889674592383929 1186258925917255944287947)
                      ·
                        rfl

theorem cell23_2310231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_2310231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310231 prefixEnd_2310231 := by exact prefixLift 2310231
  have htrace : WordTrace (prefixWord ++ tailWord_2310231) baseStart_2310231 baseEnd_2310231 := by
    simpa [prefixWord, tailWord_2310231, baseEnd_2310231] using wordTrace_append hprefix tailTrace_2310231
  have hstable : (prefixWord ++ tailWord_2310231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310231).length < 2 ^ (prefixWord ++ tailWord_2310231).sum := by decide
  have hdescent : baseEnd_2310231 < baseStart_2310231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310244 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_2310244 : Nat := 118140960795 + 2310244 * 2 ^ 59
def prefixEnd_2310244 : Nat := 4983230072969 + 3 ^ 40 * 2310244 * 2
def baseEnd_2310244 : Nat := 1186265601165764393425387

theorem tailTrace_2310244 : CollatzResearch.WordTrace tailWord_2310244 prefixEnd_2310244 1186265601165764393425387 := by
  unfold tailWord_2310244
  simp only [CollatzResearch.WordTrace]
  refine ⟨42130760521194010553960893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56174347361592014071947857 42130760521194010553960893)
  ·
    refine ⟨15799035195447753957735335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42130760521194010553960893 15799035195447753957735335)
    ·
      refine ⟨23698552793171630936603003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15799035195447753957735335 23698552793171630936603003)
      ·
        refine ⟨35547829189757446404904505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23698552793171630936603003 35547829189757446404904505)
        ·
          refine ⟨26660871892318084803678379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35547829189757446404904505 26660871892318084803678379)
          ·
            refine ⟨39991307838477127205517569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26660871892318084803678379 39991307838477127205517569)
            ·
              refine ⟨29993480878857845404138177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39991307838477127205517569 29993480878857845404138177)
              ·
                refine ⟨22495110659143384053103633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29993480878857845404138177 22495110659143384053103633)
                ·
                  refine ⟨16871332994357538039827725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22495110659143384053103633 16871332994357538039827725)
                  ·
                    refine ⟨6326749872884076764935397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16871332994357538039827725 6326749872884076764935397)
                    ·
                      refine ⟨1186265601165764393425387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6326749872884076764935397 1186265601165764393425387)
                      ·
                        rfl

theorem cell23_2310244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_2310244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310244 prefixEnd_2310244 := by exact prefixLift 2310244
  have htrace : WordTrace (prefixWord ++ tailWord_2310244) baseStart_2310244 baseEnd_2310244 := by
    simpa [prefixWord, tailWord_2310244, baseEnd_2310244] using wordTrace_append hprefix tailTrace_2310244
  have hstable : (prefixWord ++ tailWord_2310244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310244).length < 2 ^ (prefixWord ++ tailWord_2310244).sum := by decide
  have hdescent : baseEnd_2310244 < baseStart_2310244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310264 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_2310264 : Nat := 118140960795 + 2310264 * 2 ^ 59
def prefixEnd_2310264 : Nat := 4983230072969 + 3 ^ 40 * 2310264 * 2
def baseEnd_2310264 : Nat := 1186275870778854315175295

theorem tailTrace_2310264 : CollatzResearch.WordTrace tailWord_2310264 prefixEnd_2310264 1186275870778854315175295 := by
  unfold tailWord_2310264
  simp only [CollatzResearch.WordTrace]
  refine ⟨42131125251157782261824923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56174833668210376349099897 42131125251157782261824923)
  ·
    refine ⟨63196687876736673392737385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42131125251157782261824923 63196687876736673392737385)
    ·
      refine ⟨47397515907552505044553039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63196687876736673392737385 47397515907552505044553039)
      ·
        refine ⟨71096273861328757566829559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47397515907552505044553039 71096273861328757566829559)
        ·
          refine ⟨106644410791993136350244339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71096273861328757566829559 106644410791993136350244339)
          ·
            refine ⟨159966616187989704525366509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106644410791993136350244339 159966616187989704525366509)
            ·
              refine ⟨59987481070496139197012441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159966616187989704525366509 59987481070496139197012441)
              ·
                refine ⟨44990610802872104397759331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59987481070496139197012441 44990610802872104397759331)
                ·
                  refine ⟨67485916204308156596638997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44990610802872104397759331 67485916204308156596638997)
                  ·
                    refine ⟨3163402322076944840467453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67485916204308156596638997 3163402322076944840467453)
                    ·
                      refine ⟨1186275870778854315175295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3163402322076944840467453 1186275870778854315175295)
                      ·
                        rfl

theorem cell23_2310264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_2310264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310264 prefixEnd_2310264 := by exact prefixLift 2310264
  have htrace : WordTrace (prefixWord ++ tailWord_2310264) baseStart_2310264 baseEnd_2310264 := by
    simpa [prefixWord, tailWord_2310264, baseEnd_2310264] using wordTrace_append hprefix tailTrace_2310264
  have hstable : (prefixWord ++ tailWord_2310264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310264).length < 2 ^ (prefixWord ++ tailWord_2310264).sum := by decide
  have hdescent : baseEnd_2310264 < baseStart_2310264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310344 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 2, 8]
def baseStart_2310344 : Nat := 118140960795 + 2310344 * 2 ^ 59
def prefixEnd_2310344 : Nat := 4983230072969 + 3 ^ 40 * 2310344 * 2
def baseEnd_2310344 : Nat := 395438983077071334058309

theorem tailTrace_2310344 : CollatzResearch.WordTrace tailWord_2310344 prefixEnd_2310344 395438983077071334058309 := by
  unfold tailWord_2310344
  simp only [CollatzResearch.WordTrace]
  refine ⟨42132584171012869093281043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56176778894683825457708057 42132584171012869093281043)
  ·
    refine ⟨63198876256519303639921565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42132584171012869093281043 63198876256519303639921565)
    ·
      refine ⟨23699578596194738864970587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63198876256519303639921565 23699578596194738864970587)
      ·
        refine ⟨35549367894292108297455881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23699578596194738864970587 35549367894292108297455881)
        ·
          refine ⟨26662025920719081223091911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35549367894292108297455881 26662025920719081223091911)
          ·
            refine ⟨39993038881078621834637867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26662025920719081223091911 39993038881078621834637867)
            ·
              refine ⟨59989558321617932751956801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39993038881078621834637867 59989558321617932751956801)
              ·
                refine ⟨44992168741213449563967601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59989558321617932751956801 44992168741213449563967601)
                ·
                  refine ⟨33744126555910087172975701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44992168741213449563967601 33744126555910087172975701)
                  ·
                    refine ⟨395438983077071334058309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33744126555910087172975701 395438983077071334058309)
                    ·
                      rfl

theorem cell23_2310344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_2310344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310344 prefixEnd_2310344 := by exact prefixLift 2310344
  have htrace : WordTrace (prefixWord ++ tailWord_2310344) baseStart_2310344 baseEnd_2310344 := by
    simpa [prefixWord, tailWord_2310344, baseEnd_2310344] using wordTrace_append hprefix tailTrace_2310344
  have hstable : (prefixWord ++ tailWord_2310344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310344).length < 2 ^ (prefixWord ++ tailWord_2310344).sum := by decide
  have hdescent : baseEnd_2310344 < baseStart_2310344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310361 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 5, 4]
def baseStart_2310361 : Nat := 118140960795 + 2310361 * 2 ^ 59
def prefixEnd_2310361 : Nat := 4983230072969 + 3 ^ 40 * 2310361 * 2
def baseEnd_2310361 : Nat := 395441892800780145220783

theorem tailTrace_2310361 : CollatzResearch.WordTrace tailWord_2310361 prefixEnd_2310361 395441892800780145220783 := by
  unfold tailWord_2310361
  simp only [CollatzResearch.WordTrace]
  refine ⟨84265788382964150089930937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56177192255309433393287291 84265788382964150089930937)
  ·
    refine ⟨63199341287223112567448203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84265788382964150089930937 63199341287223112567448203)
    ·
      refine ⟨94799011930834668851172305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63199341287223112567448203 94799011930834668851172305)
      ·
        refine ⟨71099258948126001638379229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94799011930834668851172305 71099258948126001638379229)
        ·
          refine ⟨26662222105547250614392211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71099258948126001638379229 26662222105547250614392211)
          ·
            refine ⟨39993333158320875921588317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26662222105547250614392211 39993333158320875921588317)
            ·
              refine ⟨14997499934370328470595619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39993333158320875921588317 14997499934370328470595619)
              ·
                refine ⟨22496249901555492705893429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14997499934370328470595619 22496249901555492705893429)
                ·
                  refine ⟨2109023428270827441177509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22496249901555492705893429 2109023428270827441177509)
                  ·
                    refine ⟨395441892800780145220783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2109023428270827441177509 395441892800780145220783)
                    ·
                      rfl

theorem cell23_2310361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 4].length) (baseStart_2310361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310361 prefixEnd_2310361 := by exact prefixLift 2310361
  have htrace : WordTrace (prefixWord ++ tailWord_2310361) baseStart_2310361 baseEnd_2310361 := by
    simpa [prefixWord, tailWord_2310361, baseEnd_2310361] using wordTrace_append hprefix tailTrace_2310361
  have hstable : (prefixWord ++ tailWord_2310361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310361).length < 2 ^ (prefixWord ++ tailWord_2310361).sum := by decide
  have hdescent : baseEnd_2310361 < baseStart_2310361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310365 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2310365 : Nat := 118140960795 + 2310365 * 2 ^ 59
def prefixEnd_2310365 : Nat := 4983230072969 + 3 ^ 40 * 2310365 * 2
def baseEnd_2310365 : Nat := 395442577441652806670777

theorem tailTrace_2310365 : CollatzResearch.WordTrace tailWord_2310365 prefixEnd_2310365 395442577441652806670777 := by
  unfold tailWord_2310365
  simp only [CollatzResearch.WordTrace]
  refine ⟨84265934274949658773076549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56177289516633105848717699 84265934274949658773076549)
  ·
    refine ⟨15799862676553061019951853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84265934274949658773076549 15799862676553061019951853)
    ·
      refine ⟨5924948503707397882481945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15799862676553061019951853 5924948503707397882481945)
      ·
        refine ⟨4443711377780548411861459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5924948503707397882481945 4443711377780548411861459)
        ·
          refine ⟨6665567066670822617792189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4443711377780548411861459 6665567066670822617792189)
          ·
            refine ⟨2499587650001558481672071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6665567066670822617792189 2499587650001558481672071)
            ·
              refine ⟨3749381475002337722508107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499587650001558481672071 3749381475002337722508107)
              ·
                refine ⟨5624072212503506583762161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749381475002337722508107 5624072212503506583762161)
                ·
                  refine ⟨4218054159377629937821621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624072212503506583762161 4218054159377629937821621)
                  ·
                    refine ⟨395442577441652806670777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4218054159377629937821621 395442577441652806670777)
                    ·
                      rfl

theorem cell23_2310365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2310365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310365 prefixEnd_2310365 := by exact prefixLift 2310365
  have htrace : WordTrace (prefixWord ++ tailWord_2310365) baseStart_2310365 baseEnd_2310365 := by
    simpa [prefixWord, tailWord_2310365, baseEnd_2310365] using wordTrace_append hprefix tailTrace_2310365
  have hstable : (prefixWord ++ tailWord_2310365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310365).length < 2 ^ (prefixWord ++ tailWord_2310365).sum := by decide
  have hdescent : baseEnd_2310365 < baseStart_2310365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310421 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_2310421 : Nat := 118140960795 + 2310421 * 2 ^ 59
def prefixEnd_2310421 : Nat := 4983230072969 + 3 ^ 40 * 2310421 * 2
def baseEnd_2310421 : Nat := 395452162413870066970691

theorem tailTrace_2310421 : CollatzResearch.WordTrace tailWord_2310421 prefixEnd_2310421 395452162413870066970691 := by
  unfold tailWord_2310421
  simp only [CollatzResearch.WordTrace]
  refine ⟨84267976762746780337115117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56178651175164520224743411 84267976762746780337115117)
  ·
    refine ⟨31600491286030042626418169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84267976762746780337115117 31600491286030042626418169)
    ·
      refine ⟨23700368464522531969813627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31600491286030042626418169 23700368464522531969813627)
      ·
        refine ⟨35550552696783797954720441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23700368464522531969813627 35550552696783797954720441)
        ·
          refine ⟨26662914522587848466040331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35550552696783797954720441 26662914522587848466040331)
          ·
            refine ⟨39994371783881772699060497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26662914522587848466040331 39994371783881772699060497)
            ·
              refine ⟨29995778837911329524295373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39994371783881772699060497 29995778837911329524295373)
              ·
                refine ⟨11248417064216748571610765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29995778837911329524295373 11248417064216748571610765)
                ·
                  refine ⟨4218156399081280714354037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11248417064216748571610765 4218156399081280714354037)
                  ·
                    refine ⟨395452162413870066970691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4218156399081280714354037 395452162413870066970691)
                    ·
                      rfl

theorem cell23_2310421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_2310421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310421 prefixEnd_2310421 := by exact prefixLift 2310421
  have htrace : WordTrace (prefixWord ++ tailWord_2310421) baseStart_2310421 baseEnd_2310421 := by
    simpa [prefixWord, tailWord_2310421, baseEnd_2310421] using wordTrace_append hprefix tailTrace_2310421
  have hstable : (prefixWord ++ tailWord_2310421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310421).length < 2 ^ (prefixWord ++ tailWord_2310421).sum := by decide
  have hdescent : baseEnd_2310421 < baseStart_2310421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310429 : List Nat := [1, 4, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_2310429 : Nat := 118140960795 + 2310429 * 2 ^ 59
def prefixEnd_2310429 : Nat := 4983230072969 + 3 ^ 40 * 2310429 * 2
def baseEnd_2310429 : Nat := 395453531695615389870679

theorem tailTrace_2310429 : CollatzResearch.WordTrace tailWord_2310429 prefixEnd_2310429 395453531695615389870679 := by
  unfold tailWord_2310429
  simp only [CollatzResearch.WordTrace]
  refine ⟨84268268546717797703406341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56178845697811865135604227 84268268546717797703406341)
  ·
    refine ⟨15800300352509587069388689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84268268546717797703406341 15800300352509587069388689)
    ·
      refine ⟨11850225264382190302041517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15800300352509587069388689 11850225264382190302041517)
      ·
        refine ⟨4443834474143321363265569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11850225264382190302041517 4443834474143321363265569)
        ·
          refine ⟨3332875855607491022449177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4443834474143321363265569 3332875855607491022449177)
          ·
            refine ⟨2499656891705618266836883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3332875855607491022449177 2499656891705618266836883)
            ·
              refine ⟨3749485337558427400255325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499656891705618266836883 3749485337558427400255325)
              ·
                refine ⟨1406057001584410275095747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3749485337558427400255325 1406057001584410275095747)
                ·
                  refine ⟨2109085502376615412643621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406057001584410275095747 2109085502376615412643621)
                  ·
                    refine ⟨395453531695615389870679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2109085502376615412643621 395453531695615389870679)
                    ·
                      rfl

theorem cell23_2310429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_2310429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310429 prefixEnd_2310429 := by exact prefixLift 2310429
  have htrace : WordTrace (prefixWord ++ tailWord_2310429) baseStart_2310429 baseEnd_2310429 := by
    simpa [prefixWord, tailWord_2310429, baseEnd_2310429] using wordTrace_append hprefix tailTrace_2310429
  have hstable : (prefixWord ++ tailWord_2310429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310429).length < 2 ^ (prefixWord ++ tailWord_2310429).sum := by decide
  have hdescent : baseEnd_2310429 < baseStart_2310429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310439 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2310439 : Nat := 118140960795 + 2310439 * 2 ^ 59
def prefixEnd_2310439 : Nat := 4983230072969 + 3 ^ 40 * 2310439 * 2
def baseEnd_2310439 : Nat := 1186365729893391130486991

theorem tailTrace_2310439 : CollatzResearch.WordTrace tailWord_2310439 prefixEnd_2310439 1186365729893391130486991 := by
  unfold tailWord_2310439
  simp only [CollatzResearch.WordTrace]
  refine ⟨84268633276681569411270371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56179088851121046274180247 84268633276681569411270371)
  ·
    refine ⟨126402949915022354116905557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84268633276681569411270371 126402949915022354116905557)
    ·
      refine ⟨1481284569316668212307487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 126402949915022354116905557 1481284569316668212307487)
      ·
        refine ⟨2221926853975002318461231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481284569316668212307487 2221926853975002318461231)
        ·
          refine ⟨3332890280962503477691847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221926853975002318461231 3332890280962503477691847)
          ·
            refine ⟨4999335421443755216537771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332890280962503477691847 4999335421443755216537771)
            ·
              refine ⟨7499003132165632824806657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4999335421443755216537771 7499003132165632824806657)
              ·
                refine ⟨5624252349124224618604993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7499003132165632824806657 5624252349124224618604993)
                ·
                  refine ⟨4218189261843168463953745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624252349124224618604993 4218189261843168463953745)
                  ·
                    refine ⟨3163641946382376347965309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4218189261843168463953745 3163641946382376347965309)
                    ·
                      refine ⟨1186365729893391130486991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3163641946382376347965309 1186365729893391130486991)
                      ·
                        rfl

theorem cell23_2310439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2310439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310439 prefixEnd_2310439 := by exact prefixLift 2310439
  have htrace : WordTrace (prefixWord ++ tailWord_2310439) baseStart_2310439 baseEnd_2310439 := by
    simpa [prefixWord, tailWord_2310439, baseEnd_2310439] using wordTrace_append hprefix tailTrace_2310439
  have hstable : (prefixWord ++ tailWord_2310439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310439).length < 2 ^ (prefixWord ++ tailWord_2310439).sum := by decide
  have hdescent : baseEnd_2310439 < baseStart_2310439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310446 : List Nat := [4, 1, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2310446 : Nat := 118140960795 + 2310446 * 2 ^ 59
def prefixEnd_2310446 : Nat := 4983230072969 + 3 ^ 40 * 2310446 * 2
def baseEnd_2310446 : Nat := 395456441419324201033153

theorem tailTrace_2310446 : CollatzResearch.WordTrace tailWord_2310446 prefixEnd_2310446 395456441419324201033153 := by
  unfold tailWord_2310446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10533611073457026200846899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56179259058437473071183461 10533611073457026200846899)
  ·
    refine ⟨15800416610185539301270349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10533611073457026200846899 15800416610185539301270349)
    ·
      refine ⟨5925156228819577237976381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15800416610185539301270349 5925156228819577237976381)
      ·
        refine ⟨2221933585807341464241143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5925156228819577237976381 2221933585807341464241143)
        ·
          refine ⟨3332900378711012196361715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221933585807341464241143 3332900378711012196361715)
          ·
            refine ⟨4999350568066518294542573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332900378711012196361715 4999350568066518294542573)
            ·
              refine ⟨1874756463024944360453465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4999350568066518294542573 1874756463024944360453465)
              ·
                refine ⟨1406067347268708270340099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874756463024944360453465 1406067347268708270340099)
                ·
                  refine ⟨2109101020903062405510149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406067347268708270340099 2109101020903062405510149)
                  ·
                    refine ⟨395456441419324201033153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2109101020903062405510149 395456441419324201033153)
                    ·
                      rfl

theorem cell23_2310446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2310446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310446 prefixEnd_2310446 := by exact prefixLift 2310446
  have htrace : WordTrace (prefixWord ++ tailWord_2310446) baseStart_2310446 baseEnd_2310446 := by
    simpa [prefixWord, tailWord_2310446, baseEnd_2310446] using wordTrace_append hprefix tailTrace_2310446
  have hstable : (prefixWord ++ tailWord_2310446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310446).length < 2 ^ (prefixWord ++ tailWord_2310446).sum := by decide
  have hdescent : baseEnd_2310446 < baseStart_2310446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310452 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2310452 : Nat := 118140960795 + 2310452 * 2 ^ 59
def prefixEnd_2310452 : Nat := 4983230072969 + 3 ^ 40 * 2310452 * 2
def baseEnd_2310452 : Nat := 1186372405141899579624431

theorem tailTrace_2310452 : CollatzResearch.WordTrace tailWord_2310452 prefixEnd_2310452 1186372405141899579624431 := by
  unfold tailWord_2310452
  simp only [CollatzResearch.WordTrace]
  refine ⟨42134553712817236315746805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56179404950422981754329073 42134553712817236315746805)
  ·
    refine ⟨3950114410576615904601263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42134553712817236315746805 3950114410576615904601263)
    ·
      refine ⟨5925171615864923856901895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3950114410576615904601263 5925171615864923856901895)
      ·
        refine ⟨8887757423797385785352843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5925171615864923856901895 8887757423797385785352843)
        ·
          refine ⟨13331636135696078678029265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8887757423797385785352843 13331636135696078678029265)
          ·
            refine ⟨9998727101772059008521949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13331636135696078678029265 9998727101772059008521949)
            ·
              refine ⟨3749522663164522128195731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9998727101772059008521949 3749522663164522128195731)
              ·
                refine ⟨5624283994746783192293597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749522663164522128195731 5624283994746783192293597)
                ·
                  refine ⟨2109106498030043697110099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5624283994746783192293597 2109106498030043697110099)
                  ·
                    refine ⟨3163659747045065545665149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109106498030043697110099 3163659747045065545665149)
                    ·
                      refine ⟨1186372405141899579624431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3163659747045065545665149 1186372405141899579624431)
                      ·
                        rfl

theorem cell23_2310452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2310452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310452 prefixEnd_2310452 := by exact prefixLift 2310452
  have htrace : WordTrace (prefixWord ++ tailWord_2310452) baseStart_2310452 baseEnd_2310452 := by
    simpa [prefixWord, tailWord_2310452, baseEnd_2310452] using wordTrace_append hprefix tailTrace_2310452
  have hstable : (prefixWord ++ tailWord_2310452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310452).length < 2 ^ (prefixWord ++ tailWord_2310452).sum := by decide
  have hdescent : baseEnd_2310452 < baseStart_2310452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310471 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_2310471 : Nat := 118140960795 + 2310471 * 2 ^ 59
def prefixEnd_2310471 : Nat := 4983230072969 + 3 ^ 40 * 2310471 * 2
def baseEnd_2310471 : Nat := 1186382161274335005286843

theorem tailTrace_2310471 : CollatzResearch.WordTrace tailWord_2310471 prefixEnd_2310471 1186382161274335005286843 := by
  unfold tailWord_2310471
  simp only [CollatzResearch.WordTrace]
  refine ⟨84269800412565638876435267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56179866941710425917623511 84269800412565638876435267)
  ·
    refine ⟨126404700618848458314652901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84269800412565638876435267 126404700618848458314652901)
    ·
      refine ⟨23700881366034085933997419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126404700618848458314652901 23700881366034085933997419)
      ·
        refine ⟨35551322049051128900996129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23700881366034085933997419 35551322049051128900996129)
        ·
          refine ⟨26663491536788346675747097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35551322049051128900996129 26663491536788346675747097)
          ·
            refine ⟨19997618652591260006810323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26663491536788346675747097 19997618652591260006810323)
            ·
              refine ⟨29996427978886890010215485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19997618652591260006810323 29996427978886890010215485)
              ·
                refine ⟨11248660492082583753830807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29996427978886890010215485 11248660492082583753830807)
                ·
                  refine ⟨16872990738123875630746211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11248660492082583753830807 16872990738123875630746211)
                  ·
                    refine ⟨25309486107185813446119317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16872990738123875630746211 25309486107185813446119317)
                    ·
                      refine ⟨1186382161274335005286843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25309486107185813446119317 1186382161274335005286843)
                      ·
                        rfl

theorem cell23_2310471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_2310471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310471 prefixEnd_2310471 := by exact prefixLift 2310471
  have htrace : WordTrace (prefixWord ++ tailWord_2310471) baseStart_2310471 baseEnd_2310471 := by
    simpa [prefixWord, tailWord_2310471, baseEnd_2310471] using wordTrace_append hprefix tailTrace_2310471
  have hstable : (prefixWord ++ tailWord_2310471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310471).length < 2 ^ (prefixWord ++ tailWord_2310471).sum := by decide
  have hdescent : baseEnd_2310471 < baseStart_2310471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310481 : List Nat := [1, 2, 2, 1, 4, 2, 2, 9]
def baseStart_2310481 : Nat := 118140960795 + 2310481 * 2 ^ 59
def prefixEnd_2310481 : Nat := 4983230072969 + 3 ^ 40 * 2310481 * 2
def baseEnd_2310481 : Nat := 43940270225217776524511

theorem tailTrace_2310481 : CollatzResearch.WordTrace tailWord_2310481 prefixEnd_2310481 43940270225217776524511 := by
  unfold tailWord_2310481
  simp only [CollatzResearch.WordTrace]
  refine ⟨84270165142529410584299297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56180110095019607056199531 84270165142529410584299297)
  ·
    refine ⟨63202623856897057938224473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84270165142529410584299297 63202623856897057938224473)
    ·
      refine ⟨47401967892672793453668355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63202623856897057938224473 47401967892672793453668355)
      ·
        refine ⟨71102951839009190180502533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47401967892672793453668355 71102951839009190180502533)
        ·
          refine ⟨13331803469814223158844225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71102951839009190180502533 13331803469814223158844225)
          ·
            refine ⟨9998852602360667369133169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13331803469814223158844225 9998852602360667369133169)
            ·
              refine ⟨7499139451770500526849877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9998852602360667369133169 7499139451770500526849877)
              ·
                refine ⟨43940270225217776524511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7499139451770500526849877 43940270225217776524511)
                ·
                  rfl

theorem cell23_2310481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 9].length) (baseStart_2310481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310481 prefixEnd_2310481 := by exact prefixLift 2310481
  have htrace : WordTrace (prefixWord ++ tailWord_2310481) baseStart_2310481 baseEnd_2310481 := by
    simpa [prefixWord, tailWord_2310481, baseEnd_2310481] using wordTrace_append hprefix tailTrace_2310481
  have hstable : (prefixWord ++ tailWord_2310481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310481).length < 2 ^ (prefixWord ++ tailWord_2310481).sum := by decide
  have hdescent : baseEnd_2310481 < baseStart_2310481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310509 : List Nat := [1, 5, 1, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_2310509 : Nat := 118140960795 + 2310509 * 2 ^ 59
def prefixEnd_2310509 : Nat := 4983230072969 + 3 ^ 40 * 2310509 * 2
def baseEnd_2310509 : Nat := 1186401673539205856611669

theorem tailTrace_2310509 : CollatzResearch.WordTrace tailWord_2310509 prefixEnd_2310509 1186401673539205856611669 := by
  unfold tailWord_2310509
  simp only [CollatzResearch.WordTrace]
  refine ⟨84271186386427971366318581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56180790924285314244212387 84271186386427971366318581)
  ·
    refine ⟨7900423723727622315592367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84271186386427971366318581 7900423723727622315592367)
    ·
      refine ⟨11850635585591433473388551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7900423723727622315592367 11850635585591433473388551)
      ·
        refine ⟨17775953378387150210082827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11850635585591433473388551 17775953378387150210082827)
        ·
          refine ⟨26663930067580725315124241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17775953378387150210082827 26663930067580725315124241)
          ·
            refine ⟨19997947550685543986343181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26663930067580725315124241 19997947550685543986343181)
            ·
              refine ⟨7499230331507078994878693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19997947550685543986343181 7499230331507078994878693)
              ·
                refine ⟨1406105687157577311539755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7499230331507078994878693 1406105687157577311539755)
                ·
                  refine ⟨2109158530736365967309633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406105687157577311539755 2109158530736365967309633)
                  ·
                    refine ⟨1581868898052274475482225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2109158530736365967309633 1581868898052274475482225)
                    ·
                      refine ⟨1186401673539205856611669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1581868898052274475482225 1186401673539205856611669)
                      ·
                        rfl

theorem cell23_2310509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_2310509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310509 prefixEnd_2310509 := by exact prefixLift 2310509
  have htrace : WordTrace (prefixWord ++ tailWord_2310509) baseStart_2310509 baseEnd_2310509 := by
    simpa [prefixWord, tailWord_2310509, baseEnd_2310509] using wordTrace_append hprefix tailTrace_2310509
  have hstable : (prefixWord ++ tailWord_2310509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310509).length < 2 ^ (prefixWord ++ tailWord_2310509).sum := by decide
  have hdescent : baseEnd_2310509 < baseStart_2310509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310521 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2310521 : Nat := 118140960795 + 2310521 * 2 ^ 59
def prefixEnd_2310521 : Nat := 4983230072969 + 3 ^ 40 * 2310521 * 2
def baseEnd_2310521 : Nat := 1186407835307059809661613

theorem tailTrace_2310521 : CollatzResearch.WordTrace tailWord_2310521 prefixEnd_2310521 1186407835307059809661613 := by
  unfold tailWord_2310521
  simp only [CollatzResearch.WordTrace]
  refine ⟨84271624062384497415755417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56181082708256331610503611 84271624062384497415755417)
  ·
    refine ⟨63203718046788373061816563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84271624062384497415755417 63203718046788373061816563)
    ·
      refine ⟨94805577070182559592724845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63203718046788373061816563 94805577070182559592724845)
      ·
        refine ⟨35552091401318459847271817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94805577070182559592724845 35552091401318459847271817)
        ·
          refine ⟨26664068550988844885453863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35552091401318459847271817 26664068550988844885453863)
          ·
            refine ⟨39996102826483267328180795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26664068550988844885453863 39996102826483267328180795)
            ·
              refine ⟨59994154239724900992271193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39996102826483267328180795 59994154239724900992271193)
              ·
                refine ⟨44995615679793675744203395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59994154239724900992271193 44995615679793675744203395)
                ·
                  refine ⟨67493423519690513616305093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44995615679793675744203395 67493423519690513616305093)
                  ·
                    refine ⟨12655016909941971303057205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67493423519690513616305093 12655016909941971303057205)
                    ·
                      refine ⟨1186407835307059809661613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12655016909941971303057205 1186407835307059809661613)
                      ·
                        rfl

theorem cell23_2310521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2310521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310521 prefixEnd_2310521 := by exact prefixLift 2310521
  have htrace : WordTrace (prefixWord ++ tailWord_2310521) baseStart_2310521 baseEnd_2310521 := by
    simpa [prefixWord, tailWord_2310521, baseEnd_2310521] using wordTrace_append hprefix tailTrace_2310521
  have hstable : (prefixWord ++ tailWord_2310521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310521).length < 2 ^ (prefixWord ++ tailWord_2310521).sum := by decide
  have hdescent : baseEnd_2310521 < baseStart_2310521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310525 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_2310525 : Nat := 118140960795 + 2310525 * 2 ^ 59
def prefixEnd_2310525 : Nat := 4983230072969 + 3 ^ 40 * 2310525 * 2
def baseEnd_2310525 : Nat := 1186409889229677794011595

theorem tailTrace_2310525 : CollatzResearch.WordTrace tailWord_2310525 prefixEnd_2310525 1186409889229677794011595 := by
  unfold tailWord_2310525
  simp only [CollatzResearch.WordTrace]
  refine ⟨84271769954370006098901029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56181179969580004065934019 84271769954370006098901029)
  ·
    refine ⟨15800956866444376143543943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84271769954370006098901029 15800956866444376143543943)
    ·
      refine ⟨23701435299666564215315915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15800956866444376143543943 23701435299666564215315915)
      ·
        refine ⟨35552152949499846322973873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23701435299666564215315915 35552152949499846322973873)
        ·
          refine ⟨26664114712124884742230405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35552152949499846322973873 26664114712124884742230405)
          ·
            refine ⟨4999521508523415889168201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26664114712124884742230405 4999521508523415889168201)
            ·
              refine ⟨3749641131392561916876151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4999521508523415889168201 3749641131392561916876151)
              ·
                refine ⟨5624461697088842875314227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749641131392561916876151 5624461697088842875314227)
                ·
                  refine ⟨8436692545633264312971341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5624461697088842875314227 8436692545633264312971341)
                  ·
                    refine ⟨3163759704612474117364253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8436692545633264312971341 3163759704612474117364253)
                    ·
                      refine ⟨1186409889229677794011595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3163759704612474117364253 1186409889229677794011595)
                      ·
                        rfl

theorem cell23_2310525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_2310525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310525 prefixEnd_2310525 := by exact prefixLift 2310525
  have htrace : WordTrace (prefixWord ++ tailWord_2310525) baseStart_2310525 baseEnd_2310525 := by
    simpa [prefixWord, tailWord_2310525, baseEnd_2310525] using wordTrace_append hprefix tailTrace_2310525
  have hstable : (prefixWord ++ tailWord_2310525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310525).length < 2 ^ (prefixWord ++ tailWord_2310525).sum := by decide
  have hdescent : baseEnd_2310525 < baseStart_2310525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310535 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_2310535 : Nat := 118140960795 + 2310535 * 2 ^ 59
def prefixEnd_2310535 : Nat := 4983230072969 + 3 ^ 40 * 2310535 * 2
def baseEnd_2310535 : Nat := 1186415024036222754886549

theorem tailTrace_2310535 : CollatzResearch.WordTrace tailWord_2310535 prefixEnd_2310535 1186415024036222754886549 := by
  unfold tailWord_2310535
  simp only [CollatzResearch.WordTrace]
  refine ⟨84272134684333777806765059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56181423122889185204510039 84272134684333777806765059)
  ·
    refine ⟨126408202026500666710147589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84272134684333777806765059 126408202026500666710147589)
    ·
      refine ⟨23701537879968875008152673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126408202026500666710147589 23701537879968875008152673)
      ·
        refine ⟨17776153409976656256114505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23701537879968875008152673 17776153409976656256114505)
        ·
          refine ⟨13332115057482492192085879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17776153409976656256114505 13332115057482492192085879)
          ·
            refine ⟨19998172586223738288128819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13332115057482492192085879 19998172586223738288128819)
            ·
              refine ⟨29997258879335607432193229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19998172586223738288128819 29997258879335607432193229)
              ·
                refine ⟨11248972079750852787072461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29997258879335607432193229 11248972079750852787072461)
                ·
                  refine ⟨4218364529906569795152173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11248972079750852787072461 4218364529906569795152173)
                  ·
                    refine ⟨1581886698714963673182065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4218364529906569795152173 1581886698714963673182065)
                    ·
                      refine ⟨1186415024036222754886549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1581886698714963673182065 1186415024036222754886549)
                      ·
                        rfl

theorem cell23_2310535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_2310535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310535 prefixEnd_2310535 := by exact prefixLift 2310535
  have htrace : WordTrace (prefixWord ++ tailWord_2310535) baseStart_2310535 baseEnd_2310535 := by
    simpa [prefixWord, tailWord_2310535, baseEnd_2310535] using wordTrace_append hprefix tailTrace_2310535
  have hstable : (prefixWord ++ tailWord_2310535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310535).length < 2 ^ (prefixWord ++ tailWord_2310535).sum := by decide
  have hdescent : baseEnd_2310535 < baseStart_2310535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310578 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2310578 : Nat := 118140960795 + 2310578 * 2 ^ 59
def prefixEnd_2310578 : Nat := 4983230072969 + 3 ^ 40 * 2310578 * 2
def baseEnd_2310578 : Nat := 1186437103704366086648851

theorem tailTrace_2310578 : CollatzResearch.WordTrace tailWord_2310578 prefixEnd_2310578 1186437103704366086648851 := by
  unfold tailWord_2310578
  simp only [CollatzResearch.WordTrace]
  refine ⟨21068425755794499037645097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56182468682118664100386925 21068425755794499037645097)
  ·
    refine ⟨15801319316845874278233823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21068425755794499037645097 15801319316845874278233823)
    ·
      refine ⟨23701978975268811417350735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15801319316845874278233823 23701978975268811417350735)
      ·
        refine ⟨35552968462903217126026103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23701978975268811417350735 35552968462903217126026103)
        ·
          refine ⟨53329452694354825689039155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35552968462903217126026103 53329452694354825689039155)
          ·
            refine ⟨79994179041532238533558733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53329452694354825689039155 79994179041532238533558733)
            ·
              refine ⟨29997817140574589450084525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79994179041532238533558733 29997817140574589450084525)
              ·
                refine ⟨11249181427715471043781697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29997817140574589450084525 11249181427715471043781697)
                ·
                  refine ⟨8436886070786603282836273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11249181427715471043781697 8436886070786603282836273)
                  ·
                    refine ⟨6327664553089952462127205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8436886070786603282836273 6327664553089952462127205)
                    ·
                      refine ⟨1186437103704366086648851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6327664553089952462127205 1186437103704366086648851)
                      ·
                        rfl

theorem cell23_2310578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2310578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310578 prefixEnd_2310578 := by exact prefixLift 2310578
  have htrace : WordTrace (prefixWord ++ tailWord_2310578) baseStart_2310578 baseEnd_2310578 := by
    simpa [prefixWord, tailWord_2310578, baseEnd_2310578] using wordTrace_append hprefix tailTrace_2310578
  have hstable : (prefixWord ++ tailWord_2310578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310578).length < 2 ^ (prefixWord ++ tailWord_2310578).sum := by decide
  have hdescent : baseEnd_2310578 < baseStart_2310578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310625 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_2310625 : Nat := 118140960795 + 2310625 * 2 ^ 59
def prefixEnd_2310625 : Nat := 4983230072969 + 3 ^ 40 * 2310625 * 2
def baseEnd_2310625 : Nat := 1186461237295127402761135

theorem tailTrace_2310625 : CollatzResearch.WordTrace tailWord_2310625 prefixEnd_2310625 1186461237295127402761135 := by
  unfold tailWord_2310625
  simp only [CollatzResearch.WordTrace]
  refine ⟨84275417254007723177541329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56183611502671815451694219 84275417254007723177541329)
  ·
    refine ⟨63206562940505792383155997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84275417254007723177541329 63206562940505792383155997)
    ·
      refine ⟨23702461102689672143683499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63206562940505792383155997 23702461102689672143683499)
      ·
        refine ⟨35553691654034508215525249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23702461102689672143683499 35553691654034508215525249)
        ·
          refine ⟨26665268740525881161643937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35553691654034508215525249 26665268740525881161643937)
          ·
            refine ⟨19998951555394410871232953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26665268740525881161643937 19998951555394410871232953)
            ·
              refine ⟨14999213666545808153424715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19998951555394410871232953 14999213666545808153424715)
              ·
                refine ⟨22498820499818712230137073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14999213666545808153424715 22498820499818712230137073)
                ·
                  refine ⟨16874115374864034172602805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22498820499818712230137073 16874115374864034172602805)
                  ·
                    refine ⟨1581948316393503203681513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16874115374864034172602805 1581948316393503203681513)
                    ·
                      refine ⟨1186461237295127402761135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1581948316393503203681513 1186461237295127402761135)
                      ·
                        rfl

theorem cell23_2310625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_2310625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310625 prefixEnd_2310625 := by exact prefixLift 2310625
  have htrace : WordTrace (prefixWord ++ tailWord_2310625) baseStart_2310625 baseEnd_2310625 := by
    simpa [prefixWord, tailWord_2310625, baseEnd_2310625] using wordTrace_append hprefix tailTrace_2310625
  have hstable : (prefixWord ++ tailWord_2310625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310625).length < 2 ^ (prefixWord ++ tailWord_2310625).sum := by decide
  have hdescent : baseEnd_2310625 < baseStart_2310625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310655 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 4]
def baseStart_2310655 : Nat := 118140960795 + 2310655 * 2 ^ 59
def prefixEnd_2310655 : Nat := 4983230072969 + 3 ^ 40 * 2310655 * 2
def baseEnd_2310655 : Nat := 1186476641714762285385997

theorem tailTrace_2310655 : CollatzResearch.WordTrace tailWord_2310655 prefixEnd_2310655 1186476641714762285385997 := by
  unfold tailWord_2310655
  simp only [CollatzResearch.WordTrace]
  refine ⟨84276511443899038301133419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56184340962599358867422279 84276511443899038301133419)
  ·
    refine ⟨126414767165848557451700129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84276511443899038301133419 126414767165848557451700129)
    ·
      refine ⟨94811075374386418088775097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126414767165848557451700129 94811075374386418088775097)
      ·
        refine ⟨71108306530789813566581323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94811075374386418088775097 71108306530789813566581323)
        ·
          refine ⟨106662459796184720349871985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71108306530789813566581323 106662459796184720349871985)
          ·
            refine ⟨79996844847138540262403989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106662459796184720349871985 79996844847138540262403989)
            ·
              refine ⟨3749852102209619074800187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79996844847138540262403989 3749852102209619074800187)
              ·
                refine ⟨5624778153314428612200281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749852102209619074800187 5624778153314428612200281)
                ·
                  refine ⟨4218583614985821459150211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624778153314428612200281 4218583614985821459150211)
                  ·
                    refine ⟨6327875422478732188725317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4218583614985821459150211 6327875422478732188725317)
                    ·
                      refine ⟨1186476641714762285385997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6327875422478732188725317 1186476641714762285385997)
                      ·
                        rfl

theorem cell23_2310655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_2310655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310655 prefixEnd_2310655 := by exact prefixLift 2310655
  have htrace : WordTrace (prefixWord ++ tailWord_2310655) baseStart_2310655 baseEnd_2310655 := by
    simpa [prefixWord, tailWord_2310655, baseEnd_2310655] using wordTrace_append hprefix tailTrace_2310655
  have hstable : (prefixWord ++ tailWord_2310655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310655).length < 2 ^ (prefixWord ++ tailWord_2310655).sum := by decide
  have hdescent : baseEnd_2310655 < baseStart_2310655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310669 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2310669 : Nat := 118140960795 + 2310669 * 2 ^ 59
def prefixEnd_2310669 : Nat := 4983230072969 + 3 ^ 40 * 2310669 * 2
def baseEnd_2310669 : Nat := 395494610147975076870311

theorem tailTrace_2310669 : CollatzResearch.WordTrace tailWord_2310669 prefixEnd_2310669 395494610147975076870311 := by
  unfold tailWord_2310669
  simp only [CollatzResearch.WordTrace]
  refine ⟨84277022065848318692143061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56184681377232212461428707 84277022065848318692143061)
  ·
    refine ⟨1975242704668319969347103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 84277022065848318692143061 1975242704668319969347103)
    ·
      refine ⟨2962864057002479954020655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975242704668319969347103 2962864057002479954020655)
      ·
        refine ⟨4444296085503719931030983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962864057002479954020655 4444296085503719931030983)
        ·
          refine ⟨6666444128255579896546475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4444296085503719931030983 6666444128255579896546475)
          ·
            refine ⟨9999666192383369844819713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6666444128255579896546475 9999666192383369844819713)
            ·
              refine ⟨7499749644287527383614785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9999666192383369844819713 7499749644287527383614785)
              ·
                refine ⟨5624812233215645537711089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7499749644287527383614785 5624812233215645537711089)
                ·
                  refine ⟨4218609174911734153283317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624812233215645537711089 4218609174911734153283317)
                  ·
                    refine ⟨395494610147975076870311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4218609174911734153283317 395494610147975076870311)
                    ·
                      rfl

theorem cell23_2310669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2310669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310669 prefixEnd_2310669 := by exact prefixLift 2310669
  have htrace : WordTrace (prefixWord ++ tailWord_2310669) baseStart_2310669 baseEnd_2310669 := by
    simpa [prefixWord, tailWord_2310669, baseEnd_2310669] using wordTrace_append hprefix tailTrace_2310669
  have hstable : (prefixWord ++ tailWord_2310669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310669).length < 2 ^ (prefixWord ++ tailWord_2310669).sum := by decide
  have hdescent : baseEnd_2310669 < baseStart_2310669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310675 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 3]
def baseStart_2310675 : Nat := 118140960795 + 2310675 * 2 ^ 59
def prefixEnd_2310675 : Nat := 4983230072969 + 3 ^ 40 * 2310675 * 2
def baseEnd_2310675 : Nat := 1186486911327852207135905

theorem tailTrace_2310675 : CollatzResearch.WordTrace tailWord_2310675 prefixEnd_2310675 1186486911327852207135905 := by
  unfold tailWord_2310675
  simp only [CollatzResearch.WordTrace]
  refine ⟨84277240903826581716861479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56184827269217721144574319 84277240903826581716861479)
  ·
    refine ⟨126415861355739872575292219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84277240903826581716861479 126415861355739872575292219)
    ·
      refine ⟨189623792033609808862938329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126415861355739872575292219 189623792033609808862938329)
      ·
        refine ⟨142217844025207356647203747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189623792033609808862938329 142217844025207356647203747)
        ·
          refine ⟨213326766037811034970805621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142217844025207356647203747 213326766037811034970805621)
          ·
            refine ⟨19999384316044784528513027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 213326766037811034970805621 19999384316044784528513027)
            ·
              refine ⟨29999076474067176792769541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19999384316044784528513027 29999076474067176792769541)
              ·
                refine ⟨5624826838887595648644289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29999076474067176792769541 5624826838887595648644289)
                ·
                  refine ⟨4218620129165696736483217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624826838887595648644289 4218620129165696736483217)
                  ·
                    refine ⟨3163965096874272552362413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4218620129165696736483217 3163965096874272552362413)
                    ·
                      refine ⟨1186486911327852207135905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3163965096874272552362413 1186486911327852207135905)
                      ·
                        rfl

theorem cell23_2310675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_2310675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310675 prefixEnd_2310675 := by exact prefixLift 2310675
  have htrace : WordTrace (prefixWord ++ tailWord_2310675) baseStart_2310675 baseEnd_2310675 := by
    simpa [prefixWord, tailWord_2310675, baseEnd_2310675] using wordTrace_append hprefix tailTrace_2310675
  have hstable : (prefixWord ++ tailWord_2310675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310675).length < 2 ^ (prefixWord ++ tailWord_2310675).sum := by decide
  have hdescent : baseEnd_2310675 < baseStart_2310675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310732 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 4, 3, 2]
def baseStart_2310732 : Nat := 118140960795 + 2310732 * 2 ^ 59
def prefixEnd_2310732 : Nat := 4983230072969 + 3 ^ 40 * 2310732 * 2
def baseEnd_2310732 : Nat := 1186516179725158484123143

theorem tailTrace_2310732 : CollatzResearch.WordTrace tailWord_2310732 prefixEnd_2310732 1186516179725158484123143 := by
  unfold tailWord_2310732
  simp only [CollatzResearch.WordTrace]
  refine ⟨42139659932310040225843225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56186213243080053634457633 42139659932310040225843225)
  ·
    refine ⟨31604744949232530169382419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42139659932310040225843225 31604744949232530169382419)
    ·
      refine ⟨47407117423848795254073629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31604744949232530169382419 47407117423848795254073629)
      ·
        refine ⟨17777669033943298220277611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47407117423848795254073629 17777669033943298220277611)
        ·
          refine ⟨26666503550914947330416417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17777669033943298220277611 26666503550914947330416417)
          ·
            refine ⟨19999877663186210497812313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26666503550914947330416417 19999877663186210497812313)
            ·
              refine ⟨14999908247389657873359235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19999877663186210497812313 14999908247389657873359235)
              ·
                refine ⟨22499862371084486810038853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14999908247389657873359235 22499862371084486810038853)
                ·
                  refine ⟨4218724194578341276882285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22499862371084486810038853 4218724194578341276882285)
                  ·
                    refine ⟨1582021572966877978830857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4218724194578341276882285 1582021572966877978830857)
                    ·
                      refine ⟨1186516179725158484123143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582021572966877978830857 1186516179725158484123143)
                      ·
                        rfl

theorem cell23_2310732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_2310732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310732 prefixEnd_2310732 := by exact prefixLift 2310732
  have htrace : WordTrace (prefixWord ++ tailWord_2310732) baseStart_2310732 baseEnd_2310732 := by
    simpa [prefixWord, tailWord_2310732, baseEnd_2310732] using wordTrace_append hprefix tailTrace_2310732
  have hstable : (prefixWord ++ tailWord_2310732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310732).length < 2 ^ (prefixWord ++ tailWord_2310732).sum := by decide
  have hdescent : baseEnd_2310732 < baseStart_2310732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310762 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_2310762 : Nat := 118140960795 + 2310762 * 2 ^ 59
def prefixEnd_2310762 : Nat := 4983230072969 + 3 ^ 40 * 2310762 * 2
def baseEnd_2310762 : Nat := 1186531584144793366748005

theorem tailTrace_2310762 : CollatzResearch.WordTrace tailWord_2310762 prefixEnd_2310762 1186531584144793366748005 := by
  unfold tailWord_2310762
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070103513627848893819635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56186942703007597050185693 21070103513627848893819635)
  ·
    refine ⟨31605155270441773340729453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21070103513627848893819635 31605155270441773340729453)
    ·
      refine ⟨11851933226415665002773545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31605155270441773340729453 11851933226415665002773545)
      ·
        refine ⟨8888949919811748752080159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11851933226415665002773545 8888949919811748752080159)
        ·
          refine ⟨13333424879717623128120239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8888949919811748752080159 13333424879717623128120239)
          ·
            refine ⟨20000137319576434692180359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13333424879717623128120239 20000137319576434692180359)
            ·
              refine ⟨30000205979364652038270539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20000137319576434692180359 30000205979364652038270539)
              ·
                refine ⟨45000308969046978057405809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30000205979364652038270539 45000308969046978057405809)
                ·
                  refine ⟨33750231726785233543054357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45000308969046978057405809 33750231726785233543054357)
                  ·
                    refine ⟨1582042112193057822330673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33750231726785233543054357 1582042112193057822330673)
                    ·
                      refine ⟨1186531584144793366748005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582042112193057822330673 1186531584144793366748005)
                      ·
                        rfl

theorem cell23_2310762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_2310762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310762 prefixEnd_2310762 := by exact prefixLift 2310762
  have htrace : WordTrace (prefixWord ++ tailWord_2310762) baseStart_2310762 baseEnd_2310762 := by
    simpa [prefixWord, tailWord_2310762, baseEnd_2310762] using wordTrace_append hprefix tailTrace_2310762
  have hstable : (prefixWord ++ tailWord_2310762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310762).length < 2 ^ (prefixWord ++ tailWord_2310762).sum := by decide
  have hdescent : baseEnd_2310762 < baseStart_2310762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310775 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_2310775 : Nat := 118140960795 + 2310775 * 2 ^ 59
def prefixEnd_2310775 : Nat := 4983230072969 + 3 ^ 40 * 2310775 * 2
def baseEnd_2310775 : Nat := 1186538259393301815885445

theorem tailTrace_2310775 : CollatzResearch.WordTrace tailWord_2310775 prefixEnd_2310775 1186538259393301815885445 := by
  unfold tailWord_2310775
  simp only [CollatzResearch.WordTrace]
  refine ⟨84280888203464298795501779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56187258802309532530334519 84280888203464298795501779)
  ·
    refine ⟨126421332305196448193252669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84280888203464298795501779 126421332305196448193252669)
    ·
      refine ⟨47407999614448668072469751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126421332305196448193252669 47407999614448668072469751)
      ·
        refine ⟨71111999421673002108704627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47407999614448668072469751 71111999421673002108704627)
        ·
          refine ⟨106667999132509503163056941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71111999421673002108704627 106667999132509503163056941)
          ·
            refine ⟨40000499674691063686146353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106667999132509503163056941 40000499674691063686146353)
            ·
              refine ⟨30000374756018297764609765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40000499674691063686146353 30000374756018297764609765)
              ·
                refine ⟨5625070266753430830864331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30000374756018297764609765 5625070266753430830864331)
                ·
                  refine ⟨8437605400130146246296497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625070266753430830864331 8437605400130146246296497)
                  ·
                    refine ⟨6328204050097609684722373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8437605400130146246296497 6328204050097609684722373)
                    ·
                      refine ⟨1186538259393301815885445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6328204050097609684722373 1186538259393301815885445)
                      ·
                        rfl

theorem cell23_2310775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_2310775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310775 prefixEnd_2310775 := by exact prefixLift 2310775
  have htrace : WordTrace (prefixWord ++ tailWord_2310775) baseStart_2310775 baseEnd_2310775 := by
    simpa [prefixWord, tailWord_2310775, baseEnd_2310775] using wordTrace_append hprefix tailTrace_2310775
  have hstable : (prefixWord ++ tailWord_2310775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310775).length < 2 ^ (prefixWord ++ tailWord_2310775).sum := by decide
  have hdescent : baseEnd_2310775 < baseStart_2310775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310795 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 3]
def baseStart_2310795 : Nat := 118140960795 + 2310795 * 2 ^ 59
def prefixEnd_2310795 : Nat := 4983230072969 + 3 ^ 40 * 2310795 * 2
def baseEnd_2310795 : Nat := 1186548529006391737635353

theorem tailTrace_2310795 : CollatzResearch.WordTrace tailWord_2310795 prefixEnd_2310795 1186548529006391737635353 := by
  unfold tailWord_2310795
  simp only [CollatzResearch.WordTrace]
  refine ⟨84281617663391842211229839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56187745108927894807486559 84281617663391842211229839)
  ·
    refine ⟨126422426495087763316844759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84281617663391842211229839 126422426495087763316844759)
    ·
      refine ⟨189633639742631644975267139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126422426495087763316844759 189633639742631644975267139)
      ·
        refine ⟨284450459613947467462900709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189633639742631644975267139 284450459613947467462900709)
        ·
          refine ⟨53334461177615150149293883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 284450459613947467462900709 53334461177615150149293883)
          ·
            refine ⟨80001691766422725223940825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53334461177615150149293883 80001691766422725223940825)
            ·
              refine ⟨60001268824817043917955619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80001691766422725223940825 60001268824817043917955619)
              ·
                refine ⟨90001903237225565876933429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60001268824817043917955619 90001903237225565876933429)
                ·
                  refine ⟨8437678428489896800962509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90001903237225565876933429 8437678428489896800962509)
                  ·
                    refine ⟨3164129410683711300360941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8437678428489896800962509 3164129410683711300360941)
                    ·
                      refine ⟨1186548529006391737635353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164129410683711300360941 1186548529006391737635353)
                      ·
                        rfl

theorem cell23_2310795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 3].length) (baseStart_2310795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310795 prefixEnd_2310795 := by exact prefixLift 2310795
  have htrace : WordTrace (prefixWord ++ tailWord_2310795) baseStart_2310795 baseEnd_2310795 := by
    simpa [prefixWord, tailWord_2310795, baseEnd_2310795] using wordTrace_append hprefix tailTrace_2310795
  have hstable : (prefixWord ++ tailWord_2310795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310795).length < 2 ^ (prefixWord ++ tailWord_2310795).sum := by decide
  have hdescent : baseEnd_2310795 < baseStart_2310795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310802 : List Nat := [3, 2, 3, 1, 2, 2, 2, 8]
def baseStart_2310802 : Nat := 118140960795 + 2310802 * 2 ^ 59
def prefixEnd_2310802 : Nat := 4983230072969 + 3 ^ 40 * 2310802 * 2
def baseEnd_2310802 : Nat := 43946374939665674453623

theorem tailTrace_2310802 : CollatzResearch.WordTrace tailWord_2310802 prefixEnd_2310802 43946374939665674453623 := by
  unfold tailWord_2310802
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070468243591620601683665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56187915316244321604489773 21070468243591620601683665)
  ·
    refine ⟨15802851182693715451262749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21070468243591620601683665 15802851182693715451262749)
    ·
      refine ⟨5926069193510143294223531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15802851182693715451262749 5926069193510143294223531)
      ·
        refine ⟨8889103790265214941335297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926069193510143294223531 8889103790265214941335297)
        ·
          refine ⟨6666827842698911206001473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8889103790265214941335297 6666827842698911206001473)
          ·
            refine ⟨5000120882024183404501105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6666827842698911206001473 5000120882024183404501105)
            ·
              refine ⟨3750090661518137553375829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5000120882024183404501105 3750090661518137553375829)
              ·
                refine ⟨43946374939665674453623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3750090661518137553375829 43946374939665674453623)
                ·
                  rfl

theorem cell23_2310802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 8].length) (baseStart_2310802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310802 prefixEnd_2310802 := by exact prefixLift 2310802
  have htrace : WordTrace (prefixWord ++ tailWord_2310802) baseStart_2310802 baseEnd_2310802 := by
    simpa [prefixWord, tailWord_2310802, baseEnd_2310802] using wordTrace_append hprefix tailTrace_2310802
  have hstable : (prefixWord ++ tailWord_2310802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310802).length < 2 ^ (prefixWord ++ tailWord_2310802).sum := by decide
  have hdescent : baseEnd_2310802 < baseStart_2310802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310816 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2310816 : Nat := 118140960795 + 2310816 * 2 ^ 59
def prefixEnd_2310816 : Nat := 4983230072969 + 3 ^ 40 * 2310816 * 2
def baseEnd_2310816 : Nat := 1186559312100136155472757

theorem tailTrace_2310816 : CollatzResearch.WordTrace tailWord_2310816 prefixEnd_2310816 1186559312100136155472757 := by
  unfold tailWord_2310816
  simp only [CollatzResearch.WordTrace]
  refine ⟨42141191798157881398872151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56188255730877175198496201 42141191798157881398872151)
  ·
    refine ⟨63211787697236822098308227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42141191798157881398872151 63211787697236822098308227)
    ·
      refine ⟨94817681545855233147462341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63211787697236822098308227 94817681545855233147462341)
      ·
        refine ⟨17778315289847856215149189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94817681545855233147462341 17778315289847856215149189)
        ·
          refine ⟨3333434116846473040340473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17778315289847856215149189 3333434116846473040340473)
          ·
            refine ⟨2500075587634854780255355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3333434116846473040340473 2500075587634854780255355)
            ·
              refine ⟨3750113381452282170383033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500075587634854780255355 3750113381452282170383033)
              ·
                refine ⟨2812585036089211627787275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750113381452282170383033 2812585036089211627787275)
                ·
                  refine ⟨4218877554133817441680913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812585036089211627787275 4218877554133817441680913)
                  ·
                    refine ⟨3164158165600363081260685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4218877554133817441680913 3164158165600363081260685)
                    ·
                      refine ⟨1186559312100136155472757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164158165600363081260685 1186559312100136155472757)
                      ·
                        rfl

theorem cell23_2310816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2310816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310816 prefixEnd_2310816 := by exact prefixLift 2310816
  have htrace : WordTrace (prefixWord ++ tailWord_2310816) baseStart_2310816 baseEnd_2310816 := by
    simpa [prefixWord, tailWord_2310816, baseEnd_2310816] using wordTrace_append hprefix tailTrace_2310816
  have hstable : (prefixWord ++ tailWord_2310816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310816).length < 2 ^ (prefixWord ++ tailWord_2310816).sum := by decide
  have hdescent : baseEnd_2310816 < baseStart_2310816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310826 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2310826 : Nat := 118140960795 + 2310826 * 2 ^ 59
def prefixEnd_2310826 : Nat := 4983230072969 + 3 ^ 40 * 2310826 * 2
def baseEnd_2310826 : Nat := 1186564446906681116347711

theorem tailTrace_2310826 : CollatzResearch.WordTrace tailWord_2310826 prefixEnd_2310826 1186564446906681116347711 := by
  unfold tailWord_2310826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070687081569883626402083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56188498884186356337072221 21070687081569883626402083)
  ·
    refine ⟨31606030622354825439603125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21070687081569883626402083 31606030622354825439603125)
    ·
      refine ⟨2963065370845764884962793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31606030622354825439603125 2963065370845764884962793)
      ·
        refine ⟨2222299028134323663722095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2963065370845764884962793 2222299028134323663722095)
        ·
          refine ⟨3333448542201485495583143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222299028134323663722095 3333448542201485495583143)
          ·
            refine ⟨5000172813302228243374715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333448542201485495583143 5000172813302228243374715)
            ·
              refine ⟨7500259219953342365062073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000172813302228243374715 7500259219953342365062073)
              ·
                refine ⟨5625194414965006773796555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7500259219953342365062073 5625194414965006773796555)
                ·
                  refine ⟨8437791622447510160694833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625194414965006773796555 8437791622447510160694833)
                  ·
                    refine ⟨6328343716835632620521125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8437791622447510160694833 6328343716835632620521125)
                    ·
                      refine ⟨1186564446906681116347711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6328343716835632620521125 1186564446906681116347711)
                      ·
                        rfl

theorem cell23_2310826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2310826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310826 prefixEnd_2310826 := by exact prefixLift 2310826
  have htrace : WordTrace (prefixWord ++ tailWord_2310826) baseStart_2310826 baseEnd_2310826 := by
    simpa [prefixWord, tailWord_2310826, baseEnd_2310826] using wordTrace_append hprefix tailTrace_2310826
  have hstable : (prefixWord ++ tailWord_2310826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310826).length < 2 ^ (prefixWord ++ tailWord_2310826).sum := by decide
  have hdescent : baseEnd_2310826 < baseStart_2310826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310829 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2310829 : Nat := 118140960795 + 2310829 * 2 ^ 59
def prefixEnd_2310829 : Nat := 4983230072969 + 3 ^ 40 * 2310829 * 2
def baseEnd_2310829 : Nat := 1186565987348644604610197

theorem tailTrace_2310829 : CollatzResearch.WordTrace tailWord_2310829 prefixEnd_2310829 1186565987348644604610197 := by
  unfold tailWord_2310829
  simp only [CollatzResearch.WordTrace]
  refine ⟨84282857745268666017967541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56188571830179110678645027 84282857745268666017967541)
  ·
    refine ⟨7901517913618937439184457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84282857745268666017967541 7901517913618937439184457)
    ·
      refine ⟨5926138435214203079388343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7901517913618937439184457 5926138435214203079388343)
      ·
        refine ⟨8889207652821304619082515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926138435214203079388343 8889207652821304619082515)
        ·
          refine ⟨13333811479231956928623773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8889207652821304619082515 13333811479231956928623773)
          ·
            refine ⟨5000179304711983848233915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13333811479231956928623773 5000179304711983848233915)
            ·
              refine ⟨7500268957067975772350873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000179304711983848233915 7500268957067975772350873)
              ·
                refine ⟨5625201717800981829263155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7500268957067975772350873 5625201717800981829263155)
                ·
                  refine ⟨8437802576701472743894733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625201717800981829263155 8437802576701472743894733)
                  ·
                    refine ⟨3164175966263052278960525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8437802576701472743894733 3164175966263052278960525)
                    ·
                      refine ⟨1186565987348644604610197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164175966263052278960525 1186565987348644604610197)
                      ·
                        rfl

theorem cell23_2310829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2310829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310829 prefixEnd_2310829 := by exact prefixLift 2310829
  have htrace : WordTrace (prefixWord ++ tailWord_2310829) baseStart_2310829 baseEnd_2310829 := by
    simpa [prefixWord, tailWord_2310829, baseEnd_2310829] using wordTrace_append hprefix tailTrace_2310829
  have hstable : (prefixWord ++ tailWord_2310829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310829).length < 2 ^ (prefixWord ++ tailWord_2310829).sum := by decide
  have hdescent : baseEnd_2310829 < baseStart_2310829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310833 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2310833 : Nat := 118140960795 + 2310833 * 2 ^ 59
def prefixEnd_2310833 : Nat := 4983230072969 + 3 ^ 40 * 2310833 * 2
def baseEnd_2310833 : Nat := 1186568041271262588960179

theorem tailTrace_2310833 : CollatzResearch.WordTrace tailWord_2310833 prefixEnd_2310833 1186568041271262588960179 := by
  unfold tailWord_2310833
  simp only [CollatzResearch.WordTrace]
  refine ⟨84283003637254174701113153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56188669091502783134075435 84283003637254174701113153)
  ·
    refine ⟨63212252727940631025834865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84283003637254174701113153 63212252727940631025834865)
    ·
      refine ⟨47409189545955473269376149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63212252727940631025834865 47409189545955473269376149)
      ·
        refine ⟨2222305759966662809502007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47409189545955473269376149 2222305759966662809502007)
        ·
          refine ⟨3333458639949994214253011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222305759966662809502007 3333458639949994214253011)
          ·
            refine ⟨5000187959924991321379517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333458639949994214253011 5000187959924991321379517)
            ·
              refine ⟨1875070484971871745517319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5000187959924991321379517 1875070484971871745517319)
              ·
                refine ⟨2812605727457807618275979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875070484971871745517319 2812605727457807618275979)
                ·
                  refine ⟨4218908591186711427413969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812605727457807618275979 4218908591186711427413969)
                  ·
                    refine ⟨3164181443390033570560477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4218908591186711427413969 3164181443390033570560477)
                    ·
                      refine ⟨1186568041271262588960179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164181443390033570560477 1186568041271262588960179)
                      ·
                        rfl

theorem cell23_2310833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2310833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310833 prefixEnd_2310833 := by exact prefixLift 2310833
  have htrace : WordTrace (prefixWord ++ tailWord_2310833) baseStart_2310833 baseEnd_2310833 := by
    simpa [prefixWord, tailWord_2310833, baseEnd_2310833] using wordTrace_append hprefix tailTrace_2310833
  have hstable : (prefixWord ++ tailWord_2310833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310833).length < 2 ^ (prefixWord ++ tailWord_2310833).sum := by decide
  have hdescent : baseEnd_2310833 < baseStart_2310833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310846 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_2310846 : Nat := 118140960795 + 2310846 * 2 ^ 59
def prefixEnd_2310846 : Nat := 4983230072969 + 3 ^ 40 * 2310846 * 2
def baseEnd_2310846 : Nat := 1186574716519771038097619

theorem tailTrace_2310846 : CollatzResearch.WordTrace tailWord_2310846 prefixEnd_2310846 1186574716519771038097619 := by
  unfold tailWord_2310846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535434723275884740167049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56188985190804718614224261 10535434723275884740167049)
  ·
    refine ⟨7901576042456913555125287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10535434723275884740167049 7901576042456913555125287)
    ·
      refine ⟨11852364063685370332687931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7901576042456913555125287 11852364063685370332687931)
      ·
        refine ⟨17778546095528055499031897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11852364063685370332687931 17778546095528055499031897)
        ·
          refine ⟨13333909571646041624273923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17778546095528055499031897 13333909571646041624273923)
          ·
            refine ⟨20000864357469062436410885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13333909571646041624273923 20000864357469062436410885)
            ·
              refine ⟨3750162067025449206827041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20000864357469062436410885 3750162067025449206827041)
              ·
                refine ⟨2812621550269086905120281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750162067025449206827041 2812621550269086905120281)
                ·
                  refine ⟨2109466162701815178840211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812621550269086905120281 2109466162701815178840211)
                  ·
                    refine ⟨3164199244052722768260317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109466162701815178840211 3164199244052722768260317)
                    ·
                      refine ⟨1186574716519771038097619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164199244052722768260317 1186574716519771038097619)
                      ·
                        rfl

theorem cell23_2310846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_2310846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310846 prefixEnd_2310846 := by exact prefixLift 2310846
  have htrace : WordTrace (prefixWord ++ tailWord_2310846) baseStart_2310846 baseEnd_2310846 := by
    simpa [prefixWord, tailWord_2310846, baseEnd_2310846] using wordTrace_append hprefix tailTrace_2310846
  have hstable : (prefixWord ++ tailWord_2310846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310846).length < 2 ^ (prefixWord ++ tailWord_2310846).sum := by decide
  have hdescent : baseEnd_2310846 < baseStart_2310846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310852 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2310852 : Nat := 118140960795 + 2310852 * 2 ^ 59
def prefixEnd_2310852 : Nat := 4983230072969 + 3 ^ 40 * 2310852 * 2
def baseEnd_2310852 : Nat := 1186577797403698014622591

theorem tailTrace_2310852 : CollatzResearch.WordTrace tailWord_2310852 prefixEnd_2310852 1186577797403698014622591 := by
  unfold tailWord_2310852
  simp only [CollatzResearch.WordTrace]
  refine ⟨42141848312092670473027405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56189131082790227297369873 42141848312092670473027405)
  ·
    refine ⟨15803193117034751427385277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42141848312092670473027405 15803193117034751427385277)
    ·
      refine ⟨5926197418888031785269479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15803193117034751427385277 5926197418888031785269479)
      ·
        refine ⟨8889296128332047677904219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926197418888031785269479 8889296128332047677904219)
        ·
          refine ⟨13333944192498071516856329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8889296128332047677904219 13333944192498071516856329)
          ·
            refine ⟨10000458144373553637642247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13333944192498071516856329 10000458144373553637642247)
            ·
              refine ⟨15000687216560330456463371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10000458144373553637642247 15000687216560330456463371)
              ·
                refine ⟨22501030824840495684695057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15000687216560330456463371 22501030824840495684695057)
                ·
                  refine ⟨16875773118630371763521293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22501030824840495684695057 16875773118630371763521293)
                  ·
                    refine ⟨6328414919486389411320485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16875773118630371763521293 6328414919486389411320485)
                    ·
                      refine ⟨1186577797403698014622591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6328414919486389411320485 1186577797403698014622591)
                      ·
                        rfl

theorem cell23_2310852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2310852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310852 prefixEnd_2310852 := by exact prefixLift 2310852
  have htrace : WordTrace (prefixWord ++ tailWord_2310852) baseStart_2310852 baseEnd_2310852 := by
    simpa [prefixWord, tailWord_2310852, baseEnd_2310852] using wordTrace_append hprefix tailTrace_2310852
  have hstable : (prefixWord ++ tailWord_2310852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310852).length < 2 ^ (prefixWord ++ tailWord_2310852).sum := by decide
  have hdescent : baseEnd_2310852 < baseStart_2310852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310855 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_2310855 : Nat := 118140960795 + 2310855 * 2 ^ 59
def prefixEnd_2310855 : Nat := 4983230072969 + 3 ^ 40 * 2310855 * 2
def baseEnd_2310855 : Nat := 1186579337845661502885077

theorem tailTrace_2310855 : CollatzResearch.WordTrace tailWord_2310855 prefixEnd_2310855 1186579337845661502885077 := by
  unfold tailWord_2310855
  simp only [CollatzResearch.WordTrace]
  refine ⟨84283806043174472458414019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56189204028782981638942679 84283806043174472458414019)
  ·
    refine ⟨126425709064761708687621029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84283806043174472458414019 126425709064761708687621029)
    ·
      refine ⟨23704820449642820378928943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126425709064761708687621029 23704820449642820378928943)
      ·
        refine ⟨35557230674464230568393415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23704820449642820378928943 35557230674464230568393415)
        ·
          refine ⟨53335846011696345852590123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35557230674464230568393415 53335846011696345852590123)
          ·
            refine ⟨80003769017544518778885185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53335846011696345852590123 80003769017544518778885185)
            ·
              refine ⟨60002826763158389084163889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80003769017544518778885185 60002826763158389084163889)
              ·
                refine ⟨45002120072368791813122917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60002826763158389084163889 45002120072368791813122917)
                ·
                  refine ⟨8437897513569148464960547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45002120072368791813122917 8437897513569148464960547)
                  ·
                    refine ⟨12656846270353722697440821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8437897513569148464960547 12656846270353722697440821)
                    ·
                      refine ⟨1186579337845661502885077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12656846270353722697440821 1186579337845661502885077)
                      ·
                        rfl

theorem cell23_2310855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_2310855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310855 prefixEnd_2310855 := by exact prefixLift 2310855
  have htrace : WordTrace (prefixWord ++ tailWord_2310855) baseStart_2310855 baseEnd_2310855 := by
    simpa [prefixWord, tailWord_2310855, baseEnd_2310855] using wordTrace_append hprefix tailTrace_2310855
  have hstable : (prefixWord ++ tailWord_2310855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310855).length < 2 ^ (prefixWord ++ tailWord_2310855).sum := by decide
  have hdescent : baseEnd_2310855 < baseStart_2310855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310862 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_2310862 : Nat := 118140960795 + 2310862 * 2 ^ 59
def prefixEnd_2310862 : Nat := 4983230072969 + 3 ^ 40 * 2310862 * 2
def baseEnd_2310862 : Nat := 395527644070080991832515

theorem tailTrace_2310862 : CollatzResearch.WordTrace tailWord_2310862 prefixEnd_2310862 395527644070080991832515 := by
  unfold tailWord_2310862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535507669268639081739855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56189374236099408435945893 10535507669268639081739855)
  ·
    refine ⟨15803261503902958622609783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10535507669268639081739855 15803261503902958622609783)
    ·
      refine ⟨23704892255854437933914675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15803261503902958622609783 23704892255854437933914675)
      ·
        refine ⟨35557338383781656900872013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23704892255854437933914675 35557338383781656900872013)
        ·
          refine ⟨13334001893918121337827005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35557338383781656900872013 13334001893918121337827005)
          ·
            refine ⟨5000250710219295501685127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13334001893918121337827005 5000250710219295501685127)
            ·
              refine ⟨7500376065328943252527691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000250710219295501685127 7500376065328943252527691)
              ·
                refine ⟨11250564097993414878791537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500376065328943252527691 11250564097993414878791537)
                ·
                  refine ⟨8437923073495061159093653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11250564097993414878791537 8437923073495061159093653)
                  ·
                    refine ⟨395527644070080991832515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8437923073495061159093653 395527644070080991832515)
                    ·
                      rfl

theorem cell23_2310862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_2310862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310862 prefixEnd_2310862 := by exact prefixLift 2310862
  have htrace : WordTrace (prefixWord ++ tailWord_2310862) baseStart_2310862 baseEnd_2310862 := by
    simpa [prefixWord, tailWord_2310862, baseEnd_2310862] using wordTrace_append hprefix tailTrace_2310862
  have hstable : (prefixWord ++ tailWord_2310862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310862).length < 2 ^ (prefixWord ++ tailWord_2310862).sum := by decide
  have hdescent : baseEnd_2310862 < baseStart_2310862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310915 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 7]
def baseStart_2310915 : Nat := 118140960795 + 2310915 * 2 ^ 59
def prefixEnd_2310915 : Nat := 4983230072969 + 3 ^ 40 * 2310915 * 2
def baseEnd_2310915 : Nat := 1186610146684931268134801

theorem tailTrace_2310915 : CollatzResearch.WordTrace tailWord_2310915 prefixEnd_2310915 1186610146684931268134801 := by
  unfold tailWord_2310915
  simp only [CollatzResearch.WordTrace]
  refine ⟨84285994422957102705598199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56190662948638068470398799 84285994422957102705598199)
  ·
    refine ⟨126428991634435654058397299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84285994422957102705598199 126428991634435654058397299)
    ·
      refine ⟨189643487451653481087595949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126428991634435654058397299 189643487451653481087595949)
      ·
        refine ⟨71116307794370055407848481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189643487451653481087595949 71116307794370055407848481)
        ·
          refine ⟨53337230845777541555886361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71116307794370055407848481 53337230845777541555886361)
          ·
            refine ⟨40002923134333156166914771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53337230845777541555886361 40002923134333156166914771)
            ·
              refine ⟨60004384701499734250372157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40002923134333156166914771 60004384701499734250372157)
              ·
                refine ⟨22501644263062400343889559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60004384701499734250372157 22501644263062400343889559)
                ·
                  refine ⟨33752466394593600515834339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22501644263062400343889559 33752466394593600515834339)
                  ·
                    refine ⟨50628699591890400773751509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33752466394593600515834339 50628699591890400773751509)
                    ·
                      refine ⟨1186610146684931268134801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50628699591890400773751509 1186610146684931268134801)
                      ·
                        rfl

theorem cell23_2310915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_2310915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310915 prefixEnd_2310915 := by exact prefixLift 2310915
  have htrace : WordTrace (prefixWord ++ tailWord_2310915) baseStart_2310915 baseEnd_2310915 := by
    simpa [prefixWord, tailWord_2310915, baseEnd_2310915] using wordTrace_append hprefix tailTrace_2310915
  have hstable : (prefixWord ++ tailWord_2310915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310915).length < 2 ^ (prefixWord ++ tailWord_2310915).sum := by decide
  have hdescent : baseEnd_2310915 < baseStart_2310915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310919 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2310919 : Nat := 118140960795 + 2310919 * 2 ^ 59
def prefixEnd_2310919 : Nat := 4983230072969 + 3 ^ 40 * 2310919 * 2
def baseEnd_2310919 : Nat := 1186612200607549252484783

theorem tailTrace_2310919 : CollatzResearch.WordTrace tailWord_2310919 prefixEnd_2310919 1186612200607549252484783 := by
  unfold tailWord_2310919
  simp only [CollatzResearch.WordTrace]
  refine ⟨84286140314942611388743811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56190760209961740925829207 84286140314942611388743811)
  ·
    refine ⟨126429210472413917083115717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84286140314942611388743811 126429210472413917083115717)
    ·
      refine ⟨23705476963577609453084197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126429210472413917083115717 23705476963577609453084197)
      ·
        refine ⟨4444776930670801772453287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23705476963577609453084197 4444776930670801772453287)
        ·
          refine ⟨6667165396006202658679931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4444776930670801772453287 6667165396006202658679931)
          ·
            refine ⟨10000748094009303988019897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667165396006202658679931 10000748094009303988019897)
            ·
              refine ⟨7500561070506977991014923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10000748094009303988019897 7500561070506977991014923)
              ·
                refine ⟨11250841605760466986522385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500561070506977991014923 11250841605760466986522385)
                ·
                  refine ⟨8438131204320350239891789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11250841605760466986522385 8438131204320350239891789)
                  ·
                    refine ⟨3164299201620131339959421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8438131204320350239891789 3164299201620131339959421)
                    ·
                      refine ⟨1186612200607549252484783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164299201620131339959421 1186612200607549252484783)
                      ·
                        rfl

theorem cell23_2310919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2310919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310919 prefixEnd_2310919 := by exact prefixLift 2310919
  have htrace : WordTrace (prefixWord ++ tailWord_2310919) baseStart_2310919 baseEnd_2310919 := by
    simpa [prefixWord, tailWord_2310919, baseEnd_2310919] using wordTrace_append hprefix tailTrace_2310919
  have hstable : (prefixWord ++ tailWord_2310919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310919).length < 2 ^ (prefixWord ++ tailWord_2310919).sum := by decide
  have hdescent : baseEnd_2310919 < baseStart_2310919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310966 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2310966 : Nat := 118140960795 + 2310966 * 2 ^ 59
def prefixEnd_2310966 : Nat := 4983230072969 + 3 ^ 40 * 2310966 * 2
def baseEnd_2310966 : Nat := 1186636334198310568597067

theorem tailTrace_2310966 : CollatzResearch.WordTrace tailWord_2310966 prefixEnd_2310966 1186636334198310568597067 := by
  unfold tailWord_2310966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5267990909110771150981547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56191903030514892277136501 5267990909110771150981547)
  ·
    refine ⟨7901986363666156726472321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5267990909110771150981547 7901986363666156726472321)
    ·
      refine ⟨5926489772749617544854241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7901986363666156726472321 5926489772749617544854241)
      ·
        refine ⟨4444867329562213158640681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5926489772749617544854241 4444867329562213158640681)
        ·
          refine ⟨3333650497171659868980511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4444867329562213158640681 3333650497171659868980511)
          ·
            refine ⟨5000475745757489803470767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333650497171659868980511 5000475745757489803470767)
            ·
              refine ⟨7500713618636234705206151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000475745757489803470767 7500713618636234705206151)
              ·
                refine ⟨11251070427954352057809227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500713618636234705206151 11251070427954352057809227)
                ·
                  refine ⟨16876605641931528086713841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11251070427954352057809227 16876605641931528086713841)
                  ·
                    refine ⟨12657454231448646065035381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16876605641931528086713841 12657454231448646065035381)
                    ·
                      refine ⟨1186636334198310568597067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12657454231448646065035381 1186636334198310568597067)
                      ·
                        rfl

theorem cell23_2310966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2310966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310966 prefixEnd_2310966 := by exact prefixLift 2310966
  have htrace : WordTrace (prefixWord ++ tailWord_2310966) baseStart_2310966 baseEnd_2310966 := by
    simpa [prefixWord, tailWord_2310966, baseEnd_2310966] using wordTrace_append hprefix tailTrace_2310966
  have hstable : (prefixWord ++ tailWord_2310966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310966).length < 2 ^ (prefixWord ++ tailWord_2310966).sum := by decide
  have hdescent : baseEnd_2310966 < baseStart_2310966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
