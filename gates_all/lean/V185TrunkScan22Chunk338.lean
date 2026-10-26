import V185TrunkScan22Chunk337

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3013838 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_3013838 : Nat := 118140960795 + 3013838 * 2 ^ 59
def prefixEnd_3013838 : Nat := 4983230072969 + 3 ^ 40 * 3013838 * 2
def baseEnd_3013838 : Nat := 343899446396729906369915

theorem tailTrace_3013838 : CollatzResearch.WordTrace tailWord_3013838 prefixEnd_3013838 343899446396729906369915 := by
  unfold tailWord_3013838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13740462806923390424544271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73282468303591415597569445 13740462806923390424544271)
  ·
    refine ⟨20610694210385085636816407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13740462806923390424544271 20610694210385085636816407)
    ·
      refine ⟨30916041315577628455224611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20610694210385085636816407 30916041315577628455224611)
      ·
        refine ⟨46374061973366442682836917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30916041315577628455224611 46374061973366442682836917)
        ·
          refine ⟨4347568310003104001515961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46374061973366442682836917 4347568310003104001515961)
          ·
            refine ⟨3260676232502328001136971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4347568310003104001515961 3260676232502328001136971)
            ·
              refine ⟨4891014348753492001705457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260676232502328001136971 4891014348753492001705457)
              ·
                refine ⟨3668260761565119001279093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4891014348753492001705457 3668260761565119001279093)
                ·
                  refine ⟨343899446396729906369915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3668260761565119001279093 343899446396729906369915)
                  ·
                    rfl

theorem cell22_3013838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_3013838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013838 prefixEnd_3013838 := by exact prefixLift 3013838
  have htrace : WordTrace (prefixWord ++ tailWord_3013838) baseStart_3013838 baseEnd_3013838 := by
    simpa [prefixWord, tailWord_3013838, baseEnd_3013838] using wordTrace_append hprefix tailTrace_3013838
  have hstable : (prefixWord ++ tailWord_3013838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013838).length < 2 ^ (prefixWord ++ tailWord_3013838).sum := by decide
  have hdescent : baseEnd_3013838 < baseStart_3013838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013876 : List Nat := [2, 6, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3013876 : Nat := 118140960795 + 3013876 * 2 ^ 59
def prefixEnd_3013876 : Nat := 4983230072969 + 3 ^ 40 * 3013876 * 2
def baseEnd_3013876 : Nat := 1031711347366770286659629

theorem tailTrace_3013876 : CollatzResearch.WordTrace tailWord_3013876 prefixEnd_3013876 1031711347366770286659629 := by
  unfold tailWord_3013876
  simp only [CollatzResearch.WordTrace]
  refine ⟨54962544214624727943118741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73283392286166303924158321 54962544214624727943118741)
  ·
    refine ⟨2576369260060534122333691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54962544214624727943118741 2576369260060534122333691)
    ·
      refine ⟨3864553890090801183500537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576369260060534122333691 3864553890090801183500537)
      ·
        refine ⟨2898415417568100887625403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3864553890090801183500537 2898415417568100887625403)
        ·
          refine ⟨4347623126352151331438105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898415417568100887625403 4347623126352151331438105)
          ·
            refine ⟨3260717344764113498578579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4347623126352151331438105 3260717344764113498578579)
            ·
              refine ⟨4891076017146170247867869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260717344764113498578579 4891076017146170247867869)
              ·
                refine ⟨1834153506429813842950451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4891076017146170247867869 1834153506429813842950451)
                ·
                  refine ⟨2751230259644720764425677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834153506429813842950451 2751230259644720764425677)
                  ·
                    refine ⟨1031711347366770286659629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751230259644720764425677 1031711347366770286659629)
                    ·
                      rfl

theorem cell22_3013876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3013876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013876 prefixEnd_3013876 := by exact prefixLift 3013876
  have htrace : WordTrace (prefixWord ++ tailWord_3013876) baseStart_3013876 baseEnd_3013876 := by
    simpa [prefixWord, tailWord_3013876, baseEnd_3013876] using wordTrace_append hprefix tailTrace_3013876
  have hstable : (prefixWord ++ tailWord_3013876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013876).length < 2 ^ (prefixWord ++ tailWord_3013876).sum := by decide
  have hdescent : baseEnd_3013876 < baseStart_3013876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014084 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3014084 : Nat := 118140960795 + 3014084 * 2 ^ 59
def prefixEnd_3014084 : Nat := 4983230072969 + 3 ^ 40 * 3014084 * 2
def baseEnd_3014084 : Nat := 1031782550017527077458991

theorem tailTrace_3014084 : CollatzResearch.WordTrace tailWord_3014084 prefixEnd_3014084 1031782550017527077458991 := by
  unfold tailWord_3014084
  simp only [CollatzResearch.WordTrace]
  refine ⟨54966337406247953704904653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73288449874997271606539537 54966337406247953704904653)
  ·
    refine ⟨20612376527342982639339245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54966337406247953704904653 20612376527342982639339245)
    ·
      refine ⟨7729641197753618489752217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20612376527342982639339245 7729641197753618489752217)
      ·
        refine ⟨5797230898315213867314163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7729641197753618489752217 5797230898315213867314163)
        ·
          refine ⟨8695846347472820800971245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5797230898315213867314163 8695846347472820800971245)
          ·
            refine ⟨3260942380302307800364217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8695846347472820800971245 3260942380302307800364217)
            ·
              refine ⟨2445706785226730850273163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3260942380302307800364217 2445706785226730850273163)
              ·
                refine ⟨3668560177840096275409745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445706785226730850273163 3668560177840096275409745)
                ·
                  refine ⟨2751420133380072206557309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668560177840096275409745 2751420133380072206557309)
                  ·
                    refine ⟨1031782550017527077458991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751420133380072206557309 1031782550017527077458991)
                    ·
                      rfl

theorem cell22_3014084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3014084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014084 prefixEnd_3014084 := by exact prefixLift 3014084
  have htrace : WordTrace (prefixWord ++ tailWord_3014084) baseStart_3014084 baseEnd_3014084 := by
    simpa [prefixWord, tailWord_3014084, baseEnd_3014084] using wordTrace_append hprefix tailTrace_3014084
  have hstable : (prefixWord ++ tailWord_3014084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014084).length < 2 ^ (prefixWord ++ tailWord_3014084).sum := by decide
  have hdescent : baseEnd_3014084 < baseStart_3014084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014129 : List Nat := [1, 2, 2, 2, 3, 4, 2, 2, 1, 3]
def baseStart_3014129 : Nat := 118140960795 + 3014129 * 2 ^ 59
def prefixEnd_3014129 : Nat := 4983230072969 + 3 ^ 40 * 3014129 * 2
def baseEnd_3014129 : Nat := 1031797954437161960083853

theorem tailTrace_3014129 : CollatzResearch.WordTrace tailWord_3014129 prefixEnd_3014129 1031797954437161960083853 := by
  unfold tailWord_3014129
  simp only [CollatzResearch.WordTrace]
  refine ⟨109934316097332880095197441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73289544064888586730131627 109934316097332880095197441)
  ·
    refine ⟨82450737072999660071398081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109934316097332880095197441 82450737072999660071398081)
    ·
      refine ⟨61838052804749745053548561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82450737072999660071398081 61838052804749745053548561)
      ·
        refine ⟨46378539603562308790161421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61838052804749745053548561 46378539603562308790161421)
        ·
          refine ⟨17391952351335865796310533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46378539603562308790161421 17391952351335865796310533)
          ·
            refine ⟨3260991065875474836808225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17391952351335865796310533 3260991065875474836808225)
            ·
              refine ⟨2445743299406606127606169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3260991065875474836808225 2445743299406606127606169)
              ·
                refine ⟨1834307474554954595704627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2445743299406606127606169 1834307474554954595704627)
                ·
                  refine ⟨2751461211832431893556941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834307474554954595704627 2751461211832431893556941)
                  ·
                    refine ⟨1031797954437161960083853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751461211832431893556941 1031797954437161960083853)
                    ·
                      rfl

theorem cell22_3014129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_3014129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014129 prefixEnd_3014129 := by exact prefixLift 3014129
  have htrace : WordTrace (prefixWord ++ tailWord_3014129) baseStart_3014129 baseEnd_3014129 := by
    simpa [prefixWord, tailWord_3014129, baseEnd_3014129] using wordTrace_append hprefix tailTrace_3014129
  have hstable : (prefixWord ++ tailWord_3014129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014129).length < 2 ^ (prefixWord ++ tailWord_3014129).sum := by decide
  have hdescent : baseEnd_3014129 < baseStart_3014129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014202 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_3014202 : Nat := 118140960795 + 3014202 * 2 ^ 59
def prefixEnd_3014202 : Nat := 4983230072969 + 3 ^ 40 * 3014202 * 2
def baseEnd_3014202 : Nat := 1031822943829014103008629

theorem tailTrace_3014202 : CollatzResearch.WordTrace tailWord_3014202 prefixEnd_3014202 1031822943829014103008629 := by
  unfold tailWord_3014202
  simp only [CollatzResearch.WordTrace]
  refine ⟨27484244656517103390651215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73291319084045609041736573 27484244656517103390651215)
  ·
    refine ⟨41226366984775655085976823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27484244656517103390651215 41226366984775655085976823)
    ·
      refine ⟨61839550477163482628965235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41226366984775655085976823 61839550477163482628965235)
      ·
        refine ⟨92759325715745223943447853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61839550477163482628965235 92759325715745223943447853)
        ·
          refine ⟨34784747143404458978792945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92759325715745223943447853 34784747143404458978792945)
          ·
            refine ⟨26088560357553344234094709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34784747143404458978792945 26088560357553344234094709)
            ·
              refine ⟨2445802533520626021946379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26088560357553344234094709 2445802533520626021946379)
              ·
                refine ⟨3668703800280939032919569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445802533520626021946379 3668703800280939032919569)
                ·
                  refine ⟨2751527850210704274689677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668703800280939032919569 2751527850210704274689677)
                  ·
                    refine ⟨1031822943829014103008629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751527850210704274689677 1031822943829014103008629)
                    ·
                      rfl

theorem cell22_3014202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_3014202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014202 prefixEnd_3014202 := by exact prefixLift 3014202
  have htrace : WordTrace (prefixWord ++ tailWord_3014202) baseStart_3014202 baseEnd_3014202 := by
    simpa [prefixWord, tailWord_3014202, baseEnd_3014202] using wordTrace_append hprefix tailTrace_3014202
  have hstable : (prefixWord ++ tailWord_3014202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014202).length < 2 ^ (prefixWord ++ tailWord_3014202).sum := by decide
  have hdescent : baseEnd_3014202 < baseStart_3014202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014221 : List Nat := [1, 6, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3014221 : Nat := 118140960795 + 3014221 * 2 ^ 59
def prefixEnd_3014221 : Nat := 4983230072969 + 3 ^ 40 * 3014221 * 2
def baseEnd_3014221 : Nat := 343943149305768128927857

theorem tailTrace_3014221 : CollatzResearch.WordTrace tailWord_3014221 prefixEnd_3014221 343943149305768128927857 := by
  unfold tailWord_3014221
  simp only [CollatzResearch.WordTrace]
  refine ⟨109937671612999579807546517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73291781075333053205031011 109937671612999579807546517)
  ·
    refine ⟨5153328356859355303478743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109937671612999579807546517 5153328356859355303478743)
    ·
      refine ⟨7729992535289032955218115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5153328356859355303478743 7729992535289032955218115)
      ·
        refine ⟨11594988802933549432827173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7729992535289032955218115 11594988802933549432827173)
        ·
          refine ⟨2174060400550040518655095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11594988802933549432827173 2174060400550040518655095)
          ·
            refine ⟨3261090600825060777982643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174060400550040518655095 3261090600825060777982643)
            ·
              refine ⟨4891635901237591166973965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261090600825060777982643 4891635901237591166973965)
              ·
                refine ⟨1834363462964096687615237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4891635901237591166973965 1834363462964096687615237)
                ·
                  refine ⟨343943149305768128927857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1834363462964096687615237 343943149305768128927857)
                  ·
                    rfl

theorem cell22_3014221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3014221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014221 prefixEnd_3014221 := by exact prefixLift 3014221
  have htrace : WordTrace (prefixWord ++ tailWord_3014221) baseStart_3014221 baseEnd_3014221 := by
    simpa [prefixWord, tailWord_3014221, baseEnd_3014221] using wordTrace_append hprefix tailTrace_3014221
  have hstable : (prefixWord ++ tailWord_3014221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014221).length < 2 ^ (prefixWord ++ tailWord_3014221).sum := by decide
  have hdescent : baseEnd_3014221 < baseStart_3014221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014243 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 7]
def baseStart_3014243 : Nat := 118140960795 + 3014243 * 2 ^ 59
def prefixEnd_3014243 : Nat := 4983230072969 + 3 ^ 40 * 3014243 * 2
def baseEnd_3014243 : Nat := 343945659655634554244501

theorem tailTrace_3014243 : CollatzResearch.WordTrace tailWord_3014243 prefixEnd_3014243 343945659655634554244501 := by
  unfold tailWord_3014243
  simp only [CollatzResearch.WordTrace]
  refine ⟨109938474018919877564847383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73292316012613251709898255 109938474018919877564847383)
  ·
    refine ⟨164907711028379816347271075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109938474018919877564847383 164907711028379816347271075)
    ·
      refine ⟨247361566542569724520906613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164907711028379816347271075 247361566542569724520906613)
      ·
        refine ⟨23190146863365911673834995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247361566542569724520906613 23190146863365911673834995)
        ·
          refine ⟨34785220295048867510752493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23190146863365911673834995 34785220295048867510752493)
          ·
            refine ⟨13044457610643325316532185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34785220295048867510752493 13044457610643325316532185)
            ·
              refine ⟨9783343207982493987399139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13044457610643325316532185 9783343207982493987399139)
              ·
                refine ⟨14675014811973740981098709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9783343207982493987399139 14675014811973740981098709)
                ·
                  refine ⟨343945659655634554244501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14675014811973740981098709 343945659655634554244501)
                  ·
                    rfl

theorem cell22_3014243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 7].length) (baseStart_3014243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014243 prefixEnd_3014243 := by exact prefixLift 3014243
  have htrace : WordTrace (prefixWord ++ tailWord_3014243) baseStart_3014243 baseEnd_3014243 := by
    simpa [prefixWord, tailWord_3014243, baseEnd_3014243] using wordTrace_append hprefix tailTrace_3014243
  have hstable : (prefixWord ++ tailWord_3014243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014243).length < 2 ^ (prefixWord ++ tailWord_3014243).sum := by decide
  have hdescent : baseEnd_3014243 < baseStart_3014243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014247 : List Nat := [1, 1, 5, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3014247 : Nat := 118140960795 + 3014247 * 2 ^ 59
def prefixEnd_3014247 : Nat := 4983230072969 + 3 ^ 40 * 3014247 * 2
def baseEnd_3014247 : Nat := 1031838348248648985633491

theorem tailTrace_3014247 : CollatzResearch.WordTrace tailWord_3014247 prefixEnd_3014247 1031838348248648985633491 := by
  unfold tailWord_3014247
  simp only [CollatzResearch.WordTrace]
  refine ⟨109938619910905386247992995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73292413273936924165328663 109938619910905386247992995)
  ·
    refine ⟨164907929866358079371989493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109938619910905386247992995 164907929866358079371989493)
    ·
      refine ⟨15460118424971069941124015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164907929866358079371989493 15460118424971069941124015)
      ·
        refine ⟨23190177637456604911686023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15460118424971069941124015 23190177637456604911686023)
        ·
          refine ⟨34785266456184907367529035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23190177637456604911686023 34785266456184907367529035)
          ·
            refine ⟨52177899684277361051293553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34785266456184907367529035 52177899684277361051293553)
            ·
              refine ⟨39133424763208020788470165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52177899684277361051293553 39133424763208020788470165)
              ·
                refine ⟨1834379285775375974459539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39133424763208020788470165 1834379285775375974459539)
                ·
                  refine ⟨2751568928663063961689309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834379285775375974459539 2751568928663063961689309)
                  ·
                    refine ⟨1031838348248648985633491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751568928663063961689309 1031838348248648985633491)
                    ·
                      rfl

theorem cell22_3014247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3014247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014247 prefixEnd_3014247 := by exact prefixLift 3014247
  have htrace : WordTrace (prefixWord ++ tailWord_3014247) baseStart_3014247 baseEnd_3014247 := by
    simpa [prefixWord, tailWord_3014247, baseEnd_3014247] using wordTrace_append hprefix tailTrace_3014247
  have hstable : (prefixWord ++ tailWord_3014247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014247).length < 2 ^ (prefixWord ++ tailWord_3014247).sum := by decide
  have hdescent : baseEnd_3014247 < baseStart_3014247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014354 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3014354 : Nat := 118140960795 + 3014354 * 2 ^ 59
def prefixEnd_3014354 : Nat := 4983230072969 + 3 ^ 40 * 3014354 * 2
def baseEnd_3014354 : Nat := 1031874976535336373208163

theorem tailTrace_3014354 : CollatzResearch.WordTrace tailWord_3014354 prefixEnd_3014354 1031874976535336373208163 := by
  unfold tailWord_3014354
  simp only [CollatzResearch.WordTrace]
  refine ⟨27485630630379435880534529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73295015014345162348092077 27485630630379435880534529)
  ·
    refine ⟨20614222972784576910400897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27485630630379435880534529 20614222972784576910400897)
    ·
      refine ⟨15460667229588432682800673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20614222972784576910400897 15460667229588432682800673)
      ·
        refine ⟨11595500422191324512100505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15460667229588432682800673 11595500422191324512100505)
        ·
          refine ⟨8696625316643493384075379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11595500422191324512100505 8696625316643493384075379)
          ·
            refine ⟨13044937974965240076113069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8696625316643493384075379 13044937974965240076113069)
            ·
              refine ⟨4891851740611965028542401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13044937974965240076113069 4891851740611965028542401)
              ·
                refine ⟨3668888805458973771406801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4891851740611965028542401 3668888805458973771406801)
                ·
                  refine ⟨2751666604094230328555101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668888805458973771406801 2751666604094230328555101)
                  ·
                    refine ⟨1031874976535336373208163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751666604094230328555101 1031874976535336373208163)
                    ·
                      rfl

theorem cell22_3014354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3014354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014354 prefixEnd_3014354 := by exact prefixLift 3014354
  have htrace : WordTrace (prefixWord ++ tailWord_3014354) baseStart_3014354 baseEnd_3014354 := by
    simpa [prefixWord, tailWord_3014354, baseEnd_3014354] using wordTrace_append hprefix tailTrace_3014354
  have hstable : (prefixWord ++ tailWord_3014354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014354).length < 2 ^ (prefixWord ++ tailWord_3014354).sum := by decide
  have hdescent : baseEnd_3014354 < baseStart_3014354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014371 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 2, 3]
def baseStart_3014371 : Nat := 118140960795 + 3014371 * 2 ^ 59
def prefixEnd_3014371 : Nat := 4983230072969 + 3 ^ 40 * 3014371 * 2
def baseEnd_3014371 : Nat := 1031880795982753995533111

theorem tailTrace_3014371 : CollatzResearch.WordTrace tailWord_3014371 prefixEnd_3014371 1031880795982753995533111 := by
  unfold tailWord_3014371
  simp only [CollatzResearch.WordTrace]
  refine ⟨109943142562456155425506967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73295428374970770283671311 109943142562456155425506967)
  ·
    refine ⟨164914713843684233138260451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109943142562456155425506967 164914713843684233138260451)
    ·
      refine ⟨247372070765526349707390677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164914713843684233138260451 247372070765526349707390677)
      ·
        refine ⟨5797782908567023821266969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 247372070765526349707390677 5797782908567023821266969)
        ·
          refine ⟨4348337181425267865950227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5797782908567023821266969 4348337181425267865950227)
          ·
            refine ⟨6522505772137901798925341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4348337181425267865950227 6522505772137901798925341)
            ·
              refine ⟨2445939664551713174597003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6522505772137901798925341 2445939664551713174597003)
              ·
                refine ⟨3668909496827569761895505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445939664551713174597003 3668909496827569761895505)
                ·
                  refine ⟨2751682122620677321421629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668909496827569761895505 2751682122620677321421629)
                  ·
                    refine ⟨1031880795982753995533111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751682122620677321421629 1031880795982753995533111)
                    ·
                      rfl

theorem cell22_3014371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 3].length) (baseStart_3014371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014371 prefixEnd_3014371 := by exact prefixLift 3014371
  have htrace : WordTrace (prefixWord ++ tailWord_3014371) baseStart_3014371 baseEnd_3014371 := by
    simpa [prefixWord, tailWord_3014371, baseEnd_3014371] using wordTrace_append hprefix tailTrace_3014371
  have hstable : (prefixWord ++ tailWord_3014371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014371).length < 2 ^ (prefixWord ++ tailWord_3014371).sum := by decide
  have hdescent : baseEnd_3014371 < baseStart_3014371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014382 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3014382 : Nat := 118140960795 + 3014382 * 2 ^ 59
def prefixEnd_3014382 : Nat := 4983230072969 + 3 ^ 40 * 3014382 * 2
def baseEnd_3014382 : Nat := 1031884561507553633508077

theorem tailTrace_3014382 : CollatzResearch.WordTrace tailWord_3014382 prefixEnd_3014382 1031884561507553633508077 := by
  unfold tailWord_3014382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13742942970677038038019675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73295695843610869536104933 13742942970677038038019675)
  ·
    refine ⟨20614414456015557057029513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13742942970677038038019675 20614414456015557057029513)
    ·
      refine ⟨15460810842011667792772135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20614414456015557057029513 15460810842011667792772135)
      ·
        refine ⟨23191216263017501689158203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15460810842011667792772135 23191216263017501689158203)
        ·
          refine ⟨34786824394526252533737305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23191216263017501689158203 34786824394526252533737305)
          ·
            refine ⟨26090118295894689400302979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34786824394526252533737305 26090118295894689400302979)
            ·
              refine ⟨39135177443842034100454469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26090118295894689400302979 39135177443842034100454469)
              ·
                refine ⟨7337845770720381393835213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39135177443842034100454469 7337845770720381393835213)
                ·
                  refine ⟨2751692164020143022688205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7337845770720381393835213 2751692164020143022688205)
                  ·
                    refine ⟨1031884561507553633508077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751692164020143022688205 1031884561507553633508077)
                    ·
                      rfl

theorem cell22_3014382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3014382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014382 prefixEnd_3014382 := by exact prefixLift 3014382
  have htrace : WordTrace (prefixWord ++ tailWord_3014382) baseStart_3014382 baseEnd_3014382 := by
    simpa [prefixWord, tailWord_3014382, baseEnd_3014382] using wordTrace_append hprefix tailTrace_3014382
  have hstable : (prefixWord ++ tailWord_3014382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014382).length < 2 ^ (prefixWord ++ tailWord_3014382).sum := by decide
  have hdescent : baseEnd_3014382 < baseStart_3014382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014399 : List Nat := [1, 1, 2, 2, 1, 3, 5, 3, 1, 3]
def baseStart_3014399 : Nat := 118140960795 + 3014399 * 2 ^ 59
def prefixEnd_3014399 : Nat := 4983230072969 + 3 ^ 40 * 3014399 * 2
def baseEnd_3014399 : Nat := 1031890380954971255833025

theorem tailTrace_3014399 : CollatzResearch.WordTrace tailWord_3014399 prefixEnd_3014399 1031890380954971255833025 := by
  unfold tailWord_3014399
  simp only [CollatzResearch.WordTrace]
  refine ⟨109944163806354716207526251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73296109204236477471684167 109944163806354716207526251)
  ·
    refine ⟨164916245709532074311289377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109944163806354716207526251 164916245709532074311289377)
    ·
      refine ⟨123687184282149055733467033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164916245709532074311289377 123687184282149055733467033)
      ·
        refine ⟨92765388211611791800100275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123687184282149055733467033 92765388211611791800100275)
        ·
          refine ⟨139148082317417687700150413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92765388211611791800100275 139148082317417687700150413)
          ·
            refine ⟨52180530869031632887556405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139148082317417687700150413 52180530869031632887556405)
            ·
              refine ⟨4891924768971715583208413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52180530869031632887556405 4891924768971715583208413)
              ·
                refine ⟨1834471788364393343703155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4891924768971715583208413 1834471788364393343703155)
                ·
                  refine ⟨2751707682546590015554733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834471788364393343703155 2751707682546590015554733)
                  ·
                    refine ⟨1031890380954971255833025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751707682546590015554733 1031890380954971255833025)
                    ·
                      rfl

theorem cell22_3014399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 3].length) (baseStart_3014399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014399 prefixEnd_3014399 := by exact prefixLift 3014399
  have htrace : WordTrace (prefixWord ++ tailWord_3014399) baseStart_3014399 baseEnd_3014399 := by
    simpa [prefixWord, tailWord_3014399, baseEnd_3014399] using wordTrace_append hprefix tailTrace_3014399
  have hstable : (prefixWord ++ tailWord_3014399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014399).length < 2 ^ (prefixWord ++ tailWord_3014399).sum := by decide
  have hdescent : baseEnd_3014399 < baseStart_3014399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014607 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 1, 5]
def baseStart_3014607 : Nat := 118140960795 + 3014607 * 2 ^ 59
def prefixEnd_3014607 : Nat := 4983230072969 + 3 ^ 40 * 3014607 * 2
def baseEnd_3014607 : Nat := 1031961583605728046632387

theorem tailTrace_3014607 : CollatzResearch.WordTrace tailWord_3014607 prefixEnd_3014607 1031961583605728046632387 := by
  unfold tailWord_3014607
  simp only [CollatzResearch.WordTrace]
  refine ⟨109951750189601167731098075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73301166793067445154065383 109951750189601167731098075)
  ·
    refine ⟨164927625284401751596647113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109951750189601167731098075 164927625284401751596647113)
    ·
      refine ⟨123695718963301313697485335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164927625284401751596647113 123695718963301313697485335)
      ·
        refine ⟨185543578444951970546228003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123695718963301313697485335 185543578444951970546228003)
        ·
          refine ⟨278315367667427955819342005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185543578444951970546228003 278315367667427955819342005)
          ·
            refine ⟨26092065718821370858063313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278315367667427955819342005 26092065718821370858063313)
            ·
              refine ⟨19569049289116028143547485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26092065718821370858063313 19569049289116028143547485)
              ·
                refine ⟨7338393483418510553830307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19569049289116028143547485 7338393483418510553830307)
                ·
                  refine ⟨11007590225127765830745461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7338393483418510553830307 11007590225127765830745461)
                  ·
                    refine ⟨1031961583605728046632387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11007590225127765830745461 1031961583605728046632387)
                    ·
                      rfl

theorem cell22_3014607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_3014607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014607 prefixEnd_3014607 := by exact prefixLift 3014607
  have htrace : WordTrace (prefixWord ++ tailWord_3014607) baseStart_3014607 baseEnd_3014607 := by
    simpa [prefixWord, tailWord_3014607, baseEnd_3014607] using wordTrace_append hprefix tailTrace_3014607
  have hstable : (prefixWord ++ tailWord_3014607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014607).length < 2 ^ (prefixWord ++ tailWord_3014607).sum := by decide
  have hdescent : baseEnd_3014607 < baseStart_3014607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014667 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 2, 6]
def baseStart_3014667 : Nat := 118140960795 + 3014667 * 2 ^ 59
def prefixEnd_3014667 : Nat := 4983230072969 + 3 ^ 40 * 3014667 * 2
def baseEnd_3014667 : Nat := 1031982122831907890132203

theorem tailTrace_3014667 : CollatzResearch.WordTrace tailWord_3014667 prefixEnd_3014667 1031982122831907890132203 := by
  unfold tailWord_3014667
  simp only [CollatzResearch.WordTrace]
  refine ⟨109953938569383797978282255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73302625712922531985521503 109953938569383797978282255)
  ·
    refine ⟨164930907854075696967423383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109953938569383797978282255 164930907854075696967423383)
    ·
      refine ⟨247396361781113545451135075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164930907854075696967423383 247396361781113545451135075)
      ·
        refine ⟨371094542671670318176702613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247396361781113545451135075 371094542671670318176702613)
        ·
          refine ⟨17395056687734546164532935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 371094542671670318176702613 17395056687734546164532935)
          ·
            refine ⟨26092585031601819246799403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17395056687734546164532935 26092585031601819246799403)
            ·
              refine ⟨39138877547402728870199105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26092585031601819246799403 39138877547402728870199105)
              ·
                refine ⟨29354158160552046652649329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39138877547402728870199105 29354158160552046652649329)
                ·
                  refine ⟨22015618620414034989486997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29354158160552046652649329 22015618620414034989486997)
                  ·
                    refine ⟨1031982122831907890132203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22015618620414034989486997 1031982122831907890132203)
                    ·
                      rfl

theorem cell22_3014667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_3014667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014667 prefixEnd_3014667 := by exact prefixLift 3014667
  have htrace : WordTrace (prefixWord ++ tailWord_3014667) baseStart_3014667 baseEnd_3014667 := by
    simpa [prefixWord, tailWord_3014667, baseEnd_3014667] using wordTrace_append hprefix tailTrace_3014667
  have hstable : (prefixWord ++ tailWord_3014667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014667).length < 2 ^ (prefixWord ++ tailWord_3014667).sum := by decide
  have hdescent : baseEnd_3014667 < baseStart_3014667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014716 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 5]
def baseStart_3014716 : Nat := 118140960795 + 3014716 * 2 ^ 59
def prefixEnd_3014716 : Nat := 4983230072969 + 3 ^ 40 * 3014716 * 2
def baseEnd_3014716 : Nat := 343999632177762698552351

theorem tailTrace_3014716 : CollatzResearch.WordTrace tailWord_3014716 prefixEnd_3014716 343999632177762698552351 := by
  unfold tailWord_3014716
  simp only [CollatzResearch.WordTrace]
  refine ⟨54977862873103139673408001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73303817164137519564544001 54977862873103139673408001)
  ·
    refine ⟨41233397154827354755056001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54977862873103139673408001 41233397154827354755056001)
    ·
      refine ⟨30925047866120516066292001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41233397154827354755056001 30925047866120516066292001)
      ·
        refine ⟨23193785899590387049719001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30925047866120516066292001 23193785899590387049719001)
        ·
          refine ⟨17395339424692790287289251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23193785899590387049719001 17395339424692790287289251)
          ·
            refine ⟨26093009137039185430933877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17395339424692790287289251 26093009137039185430933877)
            ·
              refine ⟨2446219606597423634150051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26093009137039185430933877 2446219606597423634150051)
              ·
                refine ⟨3669329409896135451225077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446219606597423634150051 3669329409896135451225077)
                ·
                  refine ⟨343999632177762698552351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3669329409896135451225077 343999632177762698552351)
                  ·
                    rfl

theorem cell22_3014716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_3014716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014716 prefixEnd_3014716 := by exact prefixLift 3014716
  have htrace : WordTrace (prefixWord ++ tailWord_3014716) baseStart_3014716 baseEnd_3014716 := by
    simpa [prefixWord, tailWord_3014716, baseEnd_3014716] using wordTrace_append hprefix tailTrace_3014716
  have hstable : (prefixWord ++ tailWord_3014716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014716).length < 2 ^ (prefixWord ++ tailWord_3014716).sum := by decide
  have hdescent : baseEnd_3014716 < baseStart_3014716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014789 : List Nat := [1, 3, 1, 1, 5, 1, 2, 8]
def baseStart_3014789 : Nat := 118140960795 + 3014789 * 2 ^ 59
def prefixEnd_3014789 : Nat := 4983230072969 + 3 ^ 40 * 3014789 * 2
def baseEnd_3014789 : Nat := 114669320658348915397981

theorem tailTrace_3014789 : CollatzResearch.WordTrace tailWord_3014789 prefixEnd_3014789 114669320658348915397981 := by
  unfold tailWord_3014789
  simp only [CollatzResearch.WordTrace]
  refine ⟨109958388274941812814223421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73305592183294541876148947 109958388274941812814223421)
  ·
    refine ⟨41234395603103179805333783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109958388274941812814223421 41234395603103179805333783)
    ·
      refine ⟨61851593404654769708000675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41234395603103179805333783 61851593404654769708000675)
      ·
        refine ⟨92777390106982154562001013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61851593404654769708000675 92777390106982154562001013)
        ·
          refine ⟨8697880322529576990187595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92777390106982154562001013 8697880322529576990187595)
          ·
            refine ⟨13046820483794365485281393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8697880322529576990187595 13046820483794365485281393)
            ·
              refine ⟨9785115362845774113961045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13046820483794365485281393 9785115362845774113961045)
              ·
                refine ⟨114669320658348915397981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9785115362845774113961045 114669320658348915397981)
                ·
                  rfl

theorem cell22_3014789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 8].length) (baseStart_3014789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014789 prefixEnd_3014789 := by exact prefixLift 3014789
  have htrace : WordTrace (prefixWord ++ tailWord_3014789) baseStart_3014789 baseEnd_3014789 := by
    simpa [prefixWord, tailWord_3014789, baseEnd_3014789] using wordTrace_append hprefix tailTrace_3014789
  have hstable : (prefixWord ++ tailWord_3014789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014789).length < 2 ^ (prefixWord ++ tailWord_3014789).sum := by decide
  have hdescent : baseEnd_3014789 < baseStart_3014789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014810 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_3014810 : Nat := 118140960795 + 3014810 * 2 ^ 59
def prefixEnd_3014810 : Nat := 4983230072969 + 3 ^ 40 * 3014810 * 2
def baseEnd_3014810 : Nat := 1032031074654303183806765

theorem tailTrace_3014810 : CollatzResearch.WordTrace tailWord_3014810 prefixEnd_3014810 1032031074654303183806765 := by
  unfold tailWord_3014810
  simp only [CollatzResearch.WordTrace]
  refine ⟨27489788551966433350184471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73306102805243822267158589 27489788551966433350184471)
  ·
    refine ⟨41234682827949650025276707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27489788551966433350184471 41234682827949650025276707)
    ·
      refine ⟨61852024241924475037915061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41234682827949650025276707 61852024241924475037915061)
      ·
        refine ⟨5798627272680419534804537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61852024241924475037915061 5798627272680419534804537)
        ·
          refine ⟨4348970454510314651103403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5798627272680419534804537 4348970454510314651103403)
          ·
            refine ⟨6523455681765471976655105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4348970454510314651103403 6523455681765471976655105)
            ·
              refine ⟨4892591761324103982491329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6523455681765471976655105 4892591761324103982491329)
              ·
                refine ⟨3669443820993077986868497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4892591761324103982491329 3669443820993077986868497)
                ·
                  refine ⟨2752082865744808490151373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3669443820993077986868497 2752082865744808490151373)
                  ·
                    refine ⟨1032031074654303183806765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752082865744808490151373 1032031074654303183806765)
                    ·
                      rfl

theorem cell22_3014810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_3014810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014810 prefixEnd_3014810 := by exact prefixLift 3014810
  have htrace : WordTrace (prefixWord ++ tailWord_3014810) baseStart_3014810 baseEnd_3014810 := by
    simpa [prefixWord, tailWord_3014810, baseEnd_3014810] using wordTrace_append hprefix tailTrace_3014810
  have hstable : (prefixWord ++ tailWord_3014810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014810).length < 2 ^ (prefixWord ++ tailWord_3014810).sum := by decide
  have hdescent : baseEnd_3014810 < baseStart_3014810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014821 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_3014821 : Nat := 118140960795 + 3014821 * 2 ^ 59
def prefixEnd_3014821 : Nat := 4983230072969 + 3 ^ 40 * 3014821 * 2
def baseEnd_3014821 : Nat := 1032034840179102821781731

theorem tailTrace_3014821 : CollatzResearch.WordTrace tailWord_3014821 prefixEnd_3014821 1032034840179102821781731 := by
  unfold tailWord_3014821
  simp only [CollatzResearch.WordTrace]
  refine ⟨109959555410825882279388317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73306370273883921519592211 109959555410825882279388317)
  ·
    refine ⟨41234833279059705854770619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109959555410825882279388317 41234833279059705854770619)
    ·
      refine ⟨61852249918589558782155929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41234833279059705854770619 61852249918589558782155929)
      ·
        refine ⟨46389187438942169086616947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61852249918589558782155929 46389187438942169086616947)
        ·
          refine ⟨69583781158413253629925421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46389187438942169086616947 69583781158413253629925421)
          ·
            refine ⟨26093917934404970111222033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69583781158413253629925421 26093917934404970111222033)
            ·
              refine ⟨19570438450803727583416525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26093917934404970111222033 19570438450803727583416525)
              ·
                refine ⟨7338914419051397843781197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19570438450803727583416525 7338914419051397843781197)
                ·
                  refine ⟨2752092907144274191417949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7338914419051397843781197 2752092907144274191417949)
                  ·
                    refine ⟨1032034840179102821781731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752092907144274191417949 1032034840179102821781731)
                    ·
                      rfl

theorem cell22_3014821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_3014821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014821 prefixEnd_3014821 := by exact prefixLift 3014821
  have htrace : WordTrace (prefixWord ++ tailWord_3014821) baseStart_3014821 baseEnd_3014821 := by
    simpa [prefixWord, tailWord_3014821, baseEnd_3014821] using wordTrace_append hprefix tailTrace_3014821
  have hstable : (prefixWord ++ tailWord_3014821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014821).length < 2 ^ (prefixWord ++ tailWord_3014821).sum := by decide
  have hdescent : baseEnd_3014821 < baseStart_3014821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014823 : List Nat := [1, 1, 6, 2, 2, 2, 1, 7]
def baseStart_3014823 : Nat := 118140960795 + 3014823 * 2 ^ 59
def prefixEnd_3014823 : Nat := 4983230072969 + 3 ^ 40 * 3014823 * 2
def baseEnd_3014823 : Nat := 114670613868886164803525

theorem tailTrace_3014823 : CollatzResearch.WordTrace tailWord_3014823 prefixEnd_3014823 114670613868886164803525 := by
  unfold tailWord_3014823
  simp only [CollatzResearch.WordTrace]
  refine ⟨109959628356818636620961123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73306418904545757747307415 109959628356818636620961123)
  ·
    refine ⟨164939442535227954931441685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109959628356818636620961123 164939442535227954931441685)
    ·
      refine ⟨7731536368838810387411329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164939442535227954931441685 7731536368838810387411329)
      ·
        refine ⟨5798652276629107790558497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7731536368838810387411329 5798652276629107790558497)
        ·
          refine ⟨4348989207471830842918873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5798652276629107790558497 4348989207471830842918873)
          ·
            refine ⟨3261741905603873132189155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4348989207471830842918873 3261741905603873132189155)
            ·
              refine ⟨4892612858405809698283733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261741905603873132189155 4892612858405809698283733)
              ·
                refine ⟨114670613868886164803525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4892612858405809698283733 114670613868886164803525)
                ·
                  rfl

theorem cell22_3014823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 7].length) (baseStart_3014823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014823 prefixEnd_3014823 := by exact prefixLift 3014823
  have htrace : WordTrace (prefixWord ++ tailWord_3014823) baseStart_3014823 baseEnd_3014823 := by
    simpa [prefixWord, tailWord_3014823, baseEnd_3014823] using wordTrace_append hprefix tailTrace_3014823
  have hstable : (prefixWord ++ tailWord_3014823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014823).length < 2 ^ (prefixWord ++ tailWord_3014823).sum := by decide
  have hdescent : baseEnd_3014823 < baseStart_3014823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014866 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3014866 : Nat := 118140960795 + 3014866 * 2 ^ 59
def prefixEnd_3014866 : Nat := 4983230072969 + 3 ^ 40 * 3014866 * 2
def baseEnd_3014866 : Nat := 1032050244598737704406593

theorem tailTrace_3014866 : CollatzResearch.WordTrace tailWord_3014866 prefixEnd_3014866 1032050244598737704406593 := by
  unfold tailWord_3014866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27490299173915713741194113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73307464463775236643184301 27490299173915713741194113)
  ·
    refine ⟨20617724380436785305895585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27490299173915713741194113 20617724380436785305895585)
    ·
      refine ⟨15463293285327588979421689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20617724380436785305895585 15463293285327588979421689)
      ·
        refine ⟨11597469963995691734566267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15463293285327588979421689 11597469963995691734566267)
        ·
          refine ⟨17396204945993537601849401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11597469963995691734566267 17396204945993537601849401)
          ·
            refine ⟨13047153709495153201387051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17396204945993537601849401 13047153709495153201387051)
            ·
              refine ⟨19570730564242729802080577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13047153709495153201387051 19570730564242729802080577)
              ·
                refine ⟨14678047923182047351560433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19570730564242729802080577 14678047923182047351560433)
                ·
                  refine ⟨11008535942386535513670325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14678047923182047351560433 11008535942386535513670325)
                  ·
                    refine ⟨1032050244598737704406593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11008535942386535513670325 1032050244598737704406593)
                    ·
                      rfl

theorem cell22_3014866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3014866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014866 prefixEnd_3014866 := by exact prefixLift 3014866
  have htrace : WordTrace (prefixWord ++ tailWord_3014866) baseStart_3014866 baseEnd_3014866 := by
    simpa [prefixWord, tailWord_3014866, baseEnd_3014866] using wordTrace_append hprefix tailTrace_3014866
  have hstable : (prefixWord ++ tailWord_3014866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014866).length < 2 ^ (prefixWord ++ tailWord_3014866).sum := by decide
  have hdescent : baseEnd_3014866 < baseStart_3014866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014898 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_3014898 : Nat := 118140960795 + 3014898 * 2 ^ 59
def prefixEnd_3014898 : Nat := 4983230072969 + 3 ^ 40 * 3014898 * 2
def baseEnd_3014898 : Nat := 1032061198852700287606495

theorem tailTrace_3014898 : CollatzResearch.WordTrace tailWord_3014898 prefixEnd_3014898 1032061198852700287606495 := by
  unfold tailWord_3014898
  simp only [CollatzResearch.WordTrace]
  refine ⟨27490590957886731107485337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73308242554364616286627565 27490590957886731107485337)
  ·
    refine ⟨20617943218415048330614003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27490590957886731107485337 20617943218415048330614003)
    ·
      refine ⟨30926914827622572495921005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20617943218415048330614003 30926914827622572495921005)
      ·
        refine ⟨11597593060358464685970377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30926914827622572495921005 11597593060358464685970377)
        ·
          refine ⟨8698194795268848514477783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11597593060358464685970377 8698194795268848514477783)
          ·
            refine ⟨13047292192903272771716675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698194795268848514477783 13047292192903272771716675)
            ·
              refine ⟨19570938289354909157575013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13047292192903272771716675 19570938289354909157575013)
              ·
                refine ⟨3669550929254045467045315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19570938289354909157575013 3669550929254045467045315)
                ·
                  refine ⟨5504326393881068200567973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669550929254045467045315 5504326393881068200567973)
                  ·
                    refine ⟨1032061198852700287606495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5504326393881068200567973 1032061198852700287606495)
                    ·
                      rfl

theorem cell22_3014898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_3014898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014898 prefixEnd_3014898 := by exact prefixLift 3014898
  have htrace : WordTrace (prefixWord ++ tailWord_3014898) baseStart_3014898 baseEnd_3014898 := by
    simpa [prefixWord, tailWord_3014898, baseEnd_3014898] using wordTrace_append hprefix tailTrace_3014898
  have hstable : (prefixWord ++ tailWord_3014898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014898).length < 2 ^ (prefixWord ++ tailWord_3014898).sum := by decide
  have hdescent : baseEnd_3014898 < baseStart_3014898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014911 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 6, 3]
def baseStart_3014911 : Nat := 118140960795 + 3014911 * 2 ^ 59
def prefixEnd_3014911 : Nat := 4983230072969 + 3 ^ 40 * 3014911 * 2
def baseEnd_3014911 : Nat := 1032065649018372587031455

theorem tailTrace_3014911 : CollatzResearch.WordTrace tailWord_3014911 prefixEnd_3014911 1032065649018372587031455 := by
  unfold tailWord_3014911
  simp only [CollatzResearch.WordTrace]
  refine ⟨109962837980499827650164587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73308558653666551766776391 109962837980499827650164587)
  ·
    refine ⟨164944256970749741475246881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109962837980499827650164587 164944256970749741475246881)
    ·
      refine ⟨123708192728062306106435161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164944256970749741475246881 123708192728062306106435161)
      ·
        refine ⟨92781144546046729579826371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123708192728062306106435161 92781144546046729579826371)
        ·
          refine ⟨139171716819070094369739557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92781144546046729579826371 139171716819070094369739557)
          ·
            refine ⟨26094696903575642694326167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139171716819070094369739557 26094696903575642694326167)
            ·
              refine ⟨39142045355363464041489251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26094696903575642694326167 39142045355363464041489251)
              ·
                refine ⟨58713068033045196062233877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39142045355363464041489251 58713068033045196062233877)
                ·
                  refine ⟨2752175064048993565417213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58713068033045196062233877 2752175064048993565417213)
                  ·
                    refine ⟨1032065649018372587031455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752175064048993565417213 1032065649018372587031455)
                    ·
                      rfl

theorem cell22_3014911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_3014911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014911 prefixEnd_3014911 := by exact prefixLift 3014911
  have htrace : WordTrace (prefixWord ++ tailWord_3014911) baseStart_3014911 baseEnd_3014911 := by
    simpa [prefixWord, tailWord_3014911, baseEnd_3014911] using wordTrace_append hprefix tailTrace_3014911
  have hstable : (prefixWord ++ tailWord_3014911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014911).length < 2 ^ (prefixWord ++ tailWord_3014911).sum := by decide
  have hdescent : baseEnd_3014911 < baseStart_3014911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014945 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 2, 3]
def baseStart_3014945 : Nat := 118140960795 + 3014945 * 2 ^ 59
def prefixEnd_3014945 : Nat := 4983230072969 + 3 ^ 40 * 3014945 * 2
def baseEnd_3014945 : Nat := 1032077287913207831681351

theorem tailTrace_3014945 : CollatzResearch.WordTrace tailWord_3014945 prefixEnd_3014945 1032077287913207831681351 := by
  unfold tailWord_3014945
  simp only [CollatzResearch.WordTrace]
  refine ⟨109964078062376651456902289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73309385374917767637934859 109964078062376651456902289)
  ·
    refine ⟨82473058546782488592676717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109964078062376651456902289 82473058546782488592676717)
    ·
      refine ⟨30927396955043433222253769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82473058546782488592676717 30927396955043433222253769)
      ·
        refine ⟨23195547716282574916690327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30927396955043433222253769 23195547716282574916690327)
        ·
          refine ⟨34793321574423862375035491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23195547716282574916690327 34793321574423862375035491)
          ·
            refine ⟨52189982361635793562553237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34793321574423862375035491 52189982361635793562553237)
            ·
              refine ⟨2446405423201677823244683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52189982361635793562553237 2446405423201677823244683)
              ·
                refine ⟨3669608134802516734867025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446405423201677823244683 3669608134802516734867025)
                ·
                  refine ⟨2752206101101887551150269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3669608134802516734867025 2752206101101887551150269)
                  ·
                    refine ⟨1032077287913207831681351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752206101101887551150269 1032077287913207831681351)
                    ·
                      rfl

theorem cell22_3014945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_3014945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3014945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3014945 prefixEnd_3014945 := by exact prefixLift 3014945
  have htrace : WordTrace (prefixWord ++ tailWord_3014945) baseStart_3014945 baseEnd_3014945 := by
    simpa [prefixWord, tailWord_3014945, baseEnd_3014945] using wordTrace_append hprefix tailTrace_3014945
  have hstable : (prefixWord ++ tailWord_3014945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014945).length < 2 ^ (prefixWord ++ tailWord_3014945).sum := by decide
  have hdescent : baseEnd_3014945 < baseStart_3014945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015048 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 6]
def baseStart_3015048 : Nat := 118140960795 + 3015048 * 2 ^ 59
def prefixEnd_3015048 : Nat := 4983230072969 + 3 ^ 40 * 3015048 * 2
def baseEnd_3015048 : Nat := 344037515639383298785345

theorem tailTrace_3015048 : CollatzResearch.WordTrace tailWord_3015048 prefixEnd_3015048 344037515639383298785345 := by
  unfold tailWord_3015048
  simp only [CollatzResearch.WordTrace]
  refine ⟨54983917390501750023950899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73311889854002333365267865 54983917390501750023950899)
  ·
    refine ⟨82475876085752625035926349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54983917390501750023950899 82475876085752625035926349)
    ·
      refine ⟨30928453532157234388472381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82475876085752625035926349 30928453532157234388472381)
      ·
        refine ⟨11598170074558962895677143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30928453532157234388472381 11598170074558962895677143)
        ·
          refine ⟨17397255111838444343515715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11598170074558962895677143 17397255111838444343515715)
          ·
            refine ⟨26095882667757666515273573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17397255111838444343515715 26095882667757666515273573)
            ·
              refine ⟨4892978000204562471613795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26095882667757666515273573 4892978000204562471613795)
              ·
                refine ⟨7339467000306843707420693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892978000204562471613795 7339467000306843707420693)
                ·
                  refine ⟨344037515639383298785345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7339467000306843707420693 344037515639383298785345)
                  ·
                    rfl

theorem cell22_3015048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_3015048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015048 prefixEnd_3015048 := by exact prefixLift 3015048
  have htrace : WordTrace (prefixWord ++ tailWord_3015048) baseStart_3015048 baseEnd_3015048 := by
    simpa [prefixWord, tailWord_3015048, baseEnd_3015048] using wordTrace_append hprefix tailTrace_3015048
  have hstable : (prefixWord ++ tailWord_3015048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015048).length < 2 ^ (prefixWord ++ tailWord_3015048).sum := by decide
  have hdescent : baseEnd_3015048 < baseStart_3015048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015063 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 1, 5]
def baseStart_3015063 : Nat := 118140960795 + 3015063 * 2 ^ 59
def prefixEnd_3015063 : Nat := 4983230072969 + 3 ^ 40 * 3015063 * 2
def baseEnd_3015063 : Nat := 1032117681724694857230989

theorem tailTrace_3015063 : CollatzResearch.WordTrace tailWord_3015063 prefixEnd_3015063 1032117681724694857230989 := by
  unfold tailWord_3015063
  simp only [CollatzResearch.WordTrace]
  refine ⟨109968381875949157609697843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73312254583966105073131895 109968381875949157609697843)
  ·
    refine ⟨164952572813923736414546765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109968381875949157609697843 164952572813923736414546765)
    ·
      refine ⟨61857214805221401155455037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164952572813923736414546765 61857214805221401155455037)
      ·
        refine ⟨23196455551958025433295639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61857214805221401155455037 23196455551958025433295639)
        ·
          refine ⟨34794683327937038149943459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23196455551958025433295639 34794683327937038149943459)
          ·
            refine ⟨52192024991905557224915189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34794683327937038149943459 52192024991905557224915189)
            ·
              refine ⟨4893002342991145989835799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52192024991905557224915189 4893002342991145989835799)
              ·
                refine ⟨7339503514486718984753699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893002342991145989835799 7339503514486718984753699)
                ·
                  refine ⟨11009255271730078477130549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7339503514486718984753699 11009255271730078477130549)
                  ·
                    refine ⟨1032117681724694857230989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11009255271730078477130549 1032117681724694857230989)
                    ·
                      rfl

theorem cell22_3015063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_3015063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015063 prefixEnd_3015063 := by exact prefixLift 3015063
  have htrace : WordTrace (prefixWord ++ tailWord_3015063) baseStart_3015063 baseEnd_3015063 := by
    simpa [prefixWord, tailWord_3015063, baseEnd_3015063] using wordTrace_append hprefix tailTrace_3015063
  have hstable : (prefixWord ++ tailWord_3015063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015063).length < 2 ^ (prefixWord ++ tailWord_3015063).sum := by decide
  have hdescent : baseEnd_3015063 < baseStart_3015063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015153 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_3015153 : Nat := 118140960795 + 3015153 * 2 ^ 59
def prefixEnd_3015153 : Nat := 4983230072969 + 3 ^ 40 * 3015153 * 2
def baseEnd_3015153 : Nat := 1032148490563964622480713

theorem tailTrace_3015153 : CollatzResearch.WordTrace tailWord_3015153 prefixEnd_3015153 1032148490563964622480713 := by
  unfold tailWord_3015153
  simp only [CollatzResearch.WordTrace]
  refine ⟨109971664445623102980474113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73314442963748735320316075 109971664445623102980474113)
  ·
    refine ⟨82478748334217327235355585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109971664445623102980474113 82478748334217327235355585)
    ·
      refine ⟨61859061250662995426516689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82478748334217327235355585 61859061250662995426516689)
      ·
        refine ⟨46394295937997246569887517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61859061250662995426516689 46394295937997246569887517)
        ·
          refine ⟨17397860976748967463707819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46394295937997246569887517 17397860976748967463707819)
          ·
            refine ⟨26096791465123451195561729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17397860976748967463707819 26096791465123451195561729)
            ·
              refine ⟨19572593598842588396671297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26096791465123451195561729 19572593598842588396671297)
              ·
                refine ⟨14679445199131941297503473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19572593598842588396671297 14679445199131941297503473)
                ·
                  refine ⟨11009583899348955973127605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14679445199131941297503473 11009583899348955973127605)
                  ·
                    refine ⟨1032148490563964622480713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11009583899348955973127605 1032148490563964622480713)
                    ·
                      rfl

theorem cell22_3015153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_3015153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015153 prefixEnd_3015153 := by exact prefixLift 3015153
  have htrace : WordTrace (prefixWord ++ tailWord_3015153) baseStart_3015153 baseEnd_3015153 := by
    simpa [prefixWord, tailWord_3015153, baseEnd_3015153] using wordTrace_append hprefix tailTrace_3015153
  have hstable : (prefixWord ++ tailWord_3015153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015153).length < 2 ^ (prefixWord ++ tailWord_3015153).sum := by decide
  have hdescent : baseEnd_3015153 < baseStart_3015153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015258 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_3015258 : Nat := 118140960795 + 3015258 * 2 ^ 59
def prefixEnd_3015258 : Nat := 4983230072969 + 3 ^ 40 * 3015258 * 2
def baseEnd_3015258 : Nat := 1032184434209779348605391

theorem tailTrace_3015258 : CollatzResearch.WordTrace tailWord_3015258 prefixEnd_3015258 1032184434209779348605391 := by
  unfold tailWord_3015258
  simp only [CollatzResearch.WordTrace]
  refine ⟨27493873527560676478261607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73316996073495137275364285 27493873527560676478261607)
  ·
    refine ⟨41240810291341014717392411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27493873527560676478261607 41240810291341014717392411)
    ·
      refine ⟨61861215437011522076088617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41240810291341014717392411 61861215437011522076088617)
      ·
        refine ⟨46395911577758641557066463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61861215437011522076088617 46395911577758641557066463)
        ·
          refine ⟨69593867366637962335599695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46395911577758641557066463 69593867366637962335599695)
          ·
            refine ⟨104390801049956943503399543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69593867366637962335599695 104390801049956943503399543)
            ·
              refine ⟨156586201574935415255099315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104390801049956943503399543 156586201574935415255099315)
              ·
                refine ⟨234879302362403122882648973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156586201574935415255099315 234879302362403122882648973)
                ·
                  refine ⟨88079738385901171080993365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234879302362403122882648973 88079738385901171080993365)
                  ·
                    refine ⟨1032184434209779348605391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88079738385901171080993365 1032184434209779348605391)
                    ·
                      rfl

theorem cell22_3015258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_3015258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015258 prefixEnd_3015258 := by exact prefixLift 3015258
  have htrace : WordTrace (prefixWord ++ tailWord_3015258) baseStart_3015258 baseEnd_3015258 := by
    simpa [prefixWord, tailWord_3015258, baseEnd_3015258] using wordTrace_append hprefix tailTrace_3015258
  have hstable : (prefixWord ++ tailWord_3015258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015258).length < 2 ^ (prefixWord ++ tailWord_3015258).sum := by decide
  have hdescent : baseEnd_3015258 < baseStart_3015258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015298 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3015298 : Nat := 118140960795 + 3015298 * 2 ^ 59
def prefixEnd_3015298 : Nat := 4983230072969 + 3 ^ 40 * 3015298 * 2
def baseEnd_3015298 : Nat := 1032198127027232577605269

theorem tailTrace_3015298 : CollatzResearch.WordTrace tailWord_3015298 prefixEnd_3015298 1032198127027232577605269 := by
  unfold tailWord_3015298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27494238257524448186125637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73317968686731861829668365 27494238257524448186125637)
  ·
    refine ⟨5155169673285834034898557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27494238257524448186125637 5155169673285834034898557)
    ·
      refine ⟨1933188627482187763086959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5155169673285834034898557 1933188627482187763086959)
      ·
        refine ⟨2899782941223281644630439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933188627482187763086959 2899782941223281644630439)
        ·
          refine ⟨4349674411834922466945659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899782941223281644630439 4349674411834922466945659)
          ·
            refine ⟨6524511617752383700418489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349674411834922466945659 6524511617752383700418489)
            ·
              refine ⟨4893383713314287775313867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6524511617752383700418489 4893383713314287775313867)
              ·
                refine ⟨7340075569971431662970801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893383713314287775313867 7340075569971431662970801)
                ·
                  refine ⟨5505056677478573747228101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7340075569971431662970801 5505056677478573747228101)
                  ·
                    refine ⟨1032198127027232577605269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505056677478573747228101 1032198127027232577605269)
                    ·
                      rfl

theorem cell22_3015298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3015298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015298 prefixEnd_3015298 := by exact prefixLift 3015298
  have htrace : WordTrace (prefixWord ++ tailWord_3015298) baseStart_3015298 baseEnd_3015298 := by
    simpa [prefixWord, tailWord_3015298, baseEnd_3015298] using wordTrace_append hprefix tailTrace_3015298
  have hstable : (prefixWord ++ tailWord_3015298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015298).length < 2 ^ (prefixWord ++ tailWord_3015298).sum := by decide
  have hdescent : baseEnd_3015298 < baseStart_3015298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015328 : List Nat := [2, 1, 1, 4, 4, 2, 2, 2, 1, 3]
def baseStart_3015328 : Nat := 118140960795 + 3015328 * 2 ^ 59
def prefixEnd_3015328 : Nat := 4983230072969 + 3 ^ 40 * 3015328 * 2
def baseEnd_3015328 : Nat := 1032208396640322499355177

theorem tailTrace_3015328 : CollatzResearch.WordTrace tailWord_3015328 prefixEnd_3015328 1032208396640322499355177 := by
  unfold tailWord_3015328
  simp only [CollatzResearch.WordTrace]
  refine ⟨54989023609994553934047319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73318698146659405245396425 54989023609994553934047319)
  ·
    refine ⟨82483535414991830901070979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54989023609994553934047319 82483535414991830901070979)
    ·
      refine ⟨123725303122487746351606469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82483535414991830901070979 123725303122487746351606469)
      ·
        refine ⟨23198494335466452440926213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123725303122487746351606469 23198494335466452440926213)
        ·
          refine ⟨4349717687899959832673665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23198494335466452440926213 4349717687899959832673665)
          ·
            refine ⟨3262288265924969874505249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4349717687899959832673665 3262288265924969874505249)
            ·
              refine ⟨2446716199443727405878937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3262288265924969874505249 2446716199443727405878937)
              ·
                refine ⟨1835037149582795554409203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2446716199443727405878937 1835037149582795554409203)
                ·
                  refine ⟨2752555724374193331613805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835037149582795554409203 2752555724374193331613805)
                  ·
                    refine ⟨1032208396640322499355177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752555724374193331613805 1032208396640322499355177)
                    ·
                      rfl

theorem cell22_3015328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 3].length) (baseStart_3015328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015328 prefixEnd_3015328 := by exact prefixLift 3015328
  have htrace : WordTrace (prefixWord ++ tailWord_3015328) baseStart_3015328 baseEnd_3015328 := by
    simpa [prefixWord, tailWord_3015328, baseEnd_3015328] using wordTrace_append hprefix tailTrace_3015328
  have hstable : (prefixWord ++ tailWord_3015328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015328).length < 2 ^ (prefixWord ++ tailWord_3015328).sum := by decide
  have hdescent : baseEnd_3015328 < baseStart_3015328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015384 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 2, 3]
def baseStart_3015384 : Nat := 118140960795 + 3015384 * 2 ^ 59
def prefixEnd_3015384 : Nat := 4983230072969 + 3 ^ 40 * 3015384 * 2
def baseEnd_3015384 : Nat := 1032227566584757019955005

theorem tailTrace_3015384 : CollatzResearch.WordTrace tailWord_3015384 prefixEnd_3015384 1032227566584757019955005 := by
  unfold tailWord_3015384
  simp only [CollatzResearch.WordTrace]
  refine ⟨54990044853893114716066603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73320059805190819621422137 54990044853893114716066603)
  ·
    refine ⟨82485067280839672074099905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54990044853893114716066603 82485067280839672074099905)
    ·
      refine ⟨61863800460629754055574929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82485067280839672074099905 61863800460629754055574929)
      ·
        refine ⟨46397850345472315541681197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61863800460629754055574929 46397850345472315541681197)
        ·
          refine ⟨17399193879552118328130449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46397850345472315541681197 17399193879552118328130449)
          ·
            refine ⟨13049395409664088746097837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17399193879552118328130449 13049395409664088746097837)
            ·
              refine ⟨4893523278624033279786689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13049395409664088746097837 4893523278624033279786689)
              ·
                refine ⟨3670142458968024959840017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4893523278624033279786689 3670142458968024959840017)
                ·
                  refine ⟨2752606844226018719880013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3670142458968024959840017 2752606844226018719880013)
                  ·
                    refine ⟨1032227566584757019955005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752606844226018719880013 1032227566584757019955005)
                    ·
                      rfl

theorem cell22_3015384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_3015384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015384 prefixEnd_3015384 := by exact prefixLift 3015384
  have htrace : WordTrace (prefixWord ++ tailWord_3015384) baseStart_3015384 baseEnd_3015384 := by
    simpa [prefixWord, tailWord_3015384, baseEnd_3015384] using wordTrace_append hprefix tailTrace_3015384
  have hstable : (prefixWord ++ tailWord_3015384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015384).length < 2 ^ (prefixWord ++ tailWord_3015384).sum := by decide
  have hdescent : baseEnd_3015384 < baseStart_3015384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015519 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 2, 3]
def baseStart_3015519 : Nat := 118140960795 + 3015519 * 2 ^ 59
def prefixEnd_3015519 : Nat := 4983230072969 + 3 ^ 40 * 3015519 * 2
def baseEnd_3015519 : Nat := 1032273779843661667829591

theorem tailTrace_3015519 : CollatzResearch.WordTrace tailWord_3015519 prefixEnd_3015519 1032273779843661667829591 := by
  unfold tailWord_3015519
  simp only [CollatzResearch.WordTrace]
  refine ⟨109985013562297147488297611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73323342374864764992198407 109985013562297147488297611)
  ·
    refine ⟨164977520343445721232446417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109985013562297147488297611 164977520343445721232446417)
    ·
      refine ⟨123733140257584290924334813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164977520343445721232446417 123733140257584290924334813)
      ·
        refine ⟨46399927596594109096625555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123733140257584290924334813 46399927596594109096625555)
        ·
          refine ⟨69599891394891163644938333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46399927596594109096625555 69599891394891163644938333)
          ·
            refine ⟨26099959273084186366851875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69599891394891163644938333 26099959273084186366851875)
            ·
              refine ⟨39149938909626279550277813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26099959273084186366851875 39149938909626279550277813)
              ·
                refine ⟨3670306772777463707838545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39149938909626279550277813 3670306772777463707838545)
                ·
                  refine ⟨2752730079583097780878909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3670306772777463707838545 2752730079583097780878909)
                  ·
                    refine ⟨1032273779843661667829591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752730079583097780878909 1032273779843661667829591)
                    ·
                      rfl

theorem cell22_3015519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_3015519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015519 prefixEnd_3015519 := by exact prefixLift 3015519
  have htrace : WordTrace (prefixWord ++ tailWord_3015519) baseStart_3015519 baseEnd_3015519 := by
    simpa [prefixWord, tailWord_3015519, baseEnd_3015519] using wordTrace_append hprefix tailTrace_3015519
  have hstable : (prefixWord ++ tailWord_3015519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015519).length < 2 ^ (prefixWord ++ tailWord_3015519).sum := by decide
  have hdescent : baseEnd_3015519 < baseStart_3015519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015564 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_3015564 : Nat := 118140960795 + 3015564 * 2 ^ 59
def prefixEnd_3015564 : Nat := 4983230072969 + 3 ^ 40 * 3015564 * 2
def baseEnd_3015564 : Nat := 1032289184263296550454453

theorem tailTrace_3015564 : CollatzResearch.WordTrace tailWord_3015564 prefixEnd_3015564 1032289184263296550454453 := by
  unfold tailWord_3015564
  simp only [CollatzResearch.WordTrace]
  refine ⟨54993327423567060086842873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73324436564756080115790497 54993327423567060086842873)
  ·
    refine ⟨41244995567675295065132155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54993327423567060086842873 41244995567675295065132155)
    ·
      refine ⟨61867493351512942597698233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41244995567675295065132155 61867493351512942597698233)
      ·
        refine ⟨46400620013634706948273675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61867493351512942597698233 46400620013634706948273675)
        ·
          refine ⟨69600930020452060422410513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46400620013634706948273675 69600930020452060422410513)
          ·
            refine ⟨52200697515339045316807885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69600930020452060422410513 52200697515339045316807885)
            ·
              refine ⟨19575261568252141993802957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52200697515339045316807885 19575261568252141993802957)
              ·
                refine ⟨7340723088094553247676109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19575261568252141993802957 7340723088094553247676109)
                ·
                  refine ⟨2752771158035457467878541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7340723088094553247676109 2752771158035457467878541)
                  ·
                    refine ⟨1032289184263296550454453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752771158035457467878541 1032289184263296550454453)
                    ·
                      rfl

theorem cell22_3015564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_3015564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015564 prefixEnd_3015564 := by exact prefixLift 3015564
  have htrace : WordTrace (prefixWord ++ tailWord_3015564) baseStart_3015564 baseEnd_3015564 := by
    simpa [prefixWord, tailWord_3015564, baseEnd_3015564] using wordTrace_append hprefix tailTrace_3015564
  have hstable : (prefixWord ++ tailWord_3015564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015564).length < 2 ^ (prefixWord ++ tailWord_3015564).sum := by decide
  have hdescent : baseEnd_3015564 < baseStart_3015564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015570 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3015570 : Nat := 118140960795 + 3015570 * 2 ^ 59
def prefixEnd_3015570 : Nat := 4983230072969 + 3 ^ 40 * 3015570 * 2
def baseEnd_3015570 : Nat := 1032291238185914534804435

theorem tailTrace_3015570 : CollatzResearch.WordTrace tailWord_3015570 prefixEnd_3015570 1032291238185914534804435 := by
  unfold tailWord_3015570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27496718421278095799601041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73324582456741588798936109 27496718421278095799601041)
  ·
    refine ⟨20622538815958571849700781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27496718421278095799601041 20622538815958571849700781)
    ·
      refine ⟨7733452055984464443637793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20622538815958571849700781 7733452055984464443637793)
      ·
        refine ⟨5800089041988348332728345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7733452055984464443637793 5800089041988348332728345)
        ·
          refine ⟨4350066781491261249546259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5800089041988348332728345 4350066781491261249546259)
          ·
            refine ⟨6525100172236891874319389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350066781491261249546259 6525100172236891874319389)
            ·
              refine ⟨2446912564588834452869771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6525100172236891874319389 2446912564588834452869771)
              ·
                refine ⟨3670368846883251679304657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446912564588834452869771 3670368846883251679304657)
                ·
                  refine ⟨2752776635162438759478493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3670368846883251679304657 2752776635162438759478493)
                  ·
                    refine ⟨1032291238185914534804435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752776635162438759478493 1032291238185914534804435)
                    ·
                      rfl

theorem cell22_3015570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3015570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015570 prefixEnd_3015570 := by exact prefixLift 3015570
  have htrace : WordTrace (prefixWord ++ tailWord_3015570) baseStart_3015570 baseEnd_3015570 := by
    simpa [prefixWord, tailWord_3015570, baseEnd_3015570] using wordTrace_append hprefix tailTrace_3015570
  have hstable : (prefixWord ++ tailWord_3015570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015570).length < 2 ^ (prefixWord ++ tailWord_3015570).sum := by decide
  have hdescent : baseEnd_3015570 < baseStart_3015570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015641 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_3015641 : Nat := 118140960795 + 3015641 * 2 ^ 59
def prefixEnd_3015641 : Nat := 4983230072969 + 3 ^ 40 * 3015641 * 2
def baseEnd_3015641 : Nat := 1032315542936894016279217

theorem tailTrace_3015641 : CollatzResearch.WordTrace tailWord_3015641 prefixEnd_3015641 1032315542936894016279217 := by
  unfold tailWord_3015641
  simp only [CollatzResearch.WordTrace]
  refine ⟨109989463267855162324238777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73326308845236774882825851 109989463267855162324238777)
  ·
    refine ⟨82492097450891371743179083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109989463267855162324238777 82492097450891371743179083)
    ·
      refine ⟨123738146176337057614768625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82492097450891371743179083 123738146176337057614768625)
      ·
        refine ⟨92803609632252793211076469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123738146176337057614768625 92803609632252793211076469)
        ·
          refine ⟨8700338403023699363538419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92803609632252793211076469 8700338403023699363538419)
          ·
            refine ⟨13050507604535549045307629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700338403023699363538419 13050507604535549045307629)
            ·
              refine ⟨4893940351700830891990361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13050507604535549045307629 4893940351700830891990361)
              ·
                refine ⟨3670455263775623168992771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4893940351700830891990361 3670455263775623168992771)
                ·
                  refine ⟨5505682895663434753489157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670455263775623168992771 5505682895663434753489157)
                  ·
                    refine ⟨1032315542936894016279217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505682895663434753489157 1032315542936894016279217)
                    ·
                      rfl

theorem cell22_3015641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_3015641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015641 prefixEnd_3015641 := by exact prefixLift 3015641
  have htrace : WordTrace (prefixWord ++ tailWord_3015641) baseStart_3015641 baseEnd_3015641 := by
    simpa [prefixWord, tailWord_3015641, baseEnd_3015641] using wordTrace_append hprefix tailTrace_3015641
  have hstable : (prefixWord ++ tailWord_3015641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015641).length < 2 ^ (prefixWord ++ tailWord_3015641).sum := by decide
  have hdescent : baseEnd_3015641 < baseStart_3015641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015658 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_3015658 : Nat := 118140960795 + 3015658 * 2 ^ 59
def prefixEnd_3015658 : Nat := 4983230072969 + 3 ^ 40 * 3015658 * 2
def baseEnd_3015658 : Nat := 1032321362384311638604165

theorem tailTrace_3015658 : CollatzResearch.WordTrace tailWord_3015658 prefixEnd_3015658 1032321362384311638604165 := by
  unfold tailWord_3015658
  simp only [CollatzResearch.WordTrace]
  refine ⟨27497520827198393556901907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73326722205862382818405085 27497520827198393556901907)
  ·
    refine ⟨41246281240797590335352861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27497520827198393556901907 41246281240797590335352861)
    ·
      refine ⟨15467355465299096375757323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41246281240797590335352861 15467355465299096375757323)
      ·
        refine ⟨23201033197948644563635985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15467355465299096375757323 23201033197948644563635985)
        ·
          refine ⟨17400774898461483422726989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23201033197948644563635985 17400774898461483422726989)
          ·
            refine ⟨6525290586923056283522621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17400774898461483422726989 6525290586923056283522621)
            ·
              refine ⟨2446983970096146106320983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6525290586923056283522621 2446983970096146106320983)
              ·
                refine ⟨3670475955144219159481475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446983970096146106320983 3670475955144219159481475)
                ·
                  refine ⟨5505713932716328739222213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670475955144219159481475 5505713932716328739222213)
                  ·
                    refine ⟨1032321362384311638604165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505713932716328739222213 1032321362384311638604165)
                    ·
                      rfl

theorem cell22_3015658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_3015658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015658 prefixEnd_3015658 := by exact prefixLift 3015658
  have htrace : WordTrace (prefixWord ++ tailWord_3015658) baseStart_3015658 baseEnd_3015658 := by
    simpa [prefixWord, tailWord_3015658, baseEnd_3015658] using wordTrace_append hprefix tailTrace_3015658
  have hstable : (prefixWord ++ tailWord_3015658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015658).length < 2 ^ (prefixWord ++ tailWord_3015658).sum := by decide
  have hdescent : baseEnd_3015658 < baseStart_3015658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015701 : List Nat := [1, 3, 2, 1, 4, 2, 3, 6]
def baseStart_3015701 : Nat := 118140960795 + 3015701 * 2 ^ 59
def prefixEnd_3015701 : Nat := 4983230072969 + 3 ^ 40 * 3015701 * 2
def baseEnd_3015701 : Nat := 114704009129230428864337

theorem tailTrace_3015701 : CollatzResearch.WordTrace tailWord_3015701 prefixEnd_3015701 114704009129230428864337 := by
  unfold tailWord_3015701
  simp only [CollatzResearch.WordTrace]
  refine ⟨109991651647637792571422957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73327767765091861714281971 109991651647637792571422957)
  ·
    refine ⟨41246869367864172214283609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109991651647637792571422957 41246869367864172214283609)
    ·
      refine ⟨30935152025898129160712707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41246869367864172214283609 30935152025898129160712707)
      ·
        refine ⟨46402728038847193741069061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30935152025898129160712707 46402728038847193741069061)
        ·
          refine ⟨8700511507283848826450449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46402728038847193741069061 8700511507283848826450449)
          ·
            refine ⟨6525383630462886619837837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8700511507283848826450449 6525383630462886619837837)
            ·
              refine ⟨2447018861423582482439189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6525383630462886619837837 2447018861423582482439189)
              ·
                refine ⟨114704009129230428864337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2447018861423582482439189 114704009129230428864337)
                ·
                  rfl

theorem cell22_3015701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 6].length) (baseStart_3015701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015701 prefixEnd_3015701 := by exact prefixLift 3015701
  have htrace : WordTrace (prefixWord ++ tailWord_3015701) baseStart_3015701 baseEnd_3015701 := by
    simpa [prefixWord, tailWord_3015701, baseEnd_3015701] using wordTrace_append hprefix tailTrace_3015701
  have hstable : (prefixWord ++ tailWord_3015701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015701).length < 2 ^ (prefixWord ++ tailWord_3015701).sum := by decide
  have hdescent : baseEnd_3015701 < baseStart_3015701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015703 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 2, 4]
def baseStart_3015703 : Nat := 118140960795 + 3015703 * 2 ^ 59
def prefixEnd_3015703 : Nat := 4983230072969 + 3 ^ 40 * 3015703 * 2
def baseEnd_3015703 : Nat := 1032336766803946521229027

theorem tailTrace_3015703 : CollatzResearch.WordTrace tailWord_3015703 prefixEnd_3015703 1032336766803946521229027 := by
  unfold tailWord_3015703
  simp only [CollatzResearch.WordTrace]
  refine ⟨109991724593630546912995763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73327816395753697941997175 109991724593630546912995763)
  ·
    refine ⟨164987586890445820369493645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109991724593630546912995763 164987586890445820369493645)
    ·
      refine ⟨61870345083917182638560117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164987586890445820369493645 61870345083917182638560117)
      ·
        refine ⟨5800344851617235872365011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61870345083917182638560117 5800344851617235872365011)
        ·
          refine ⟨8700517277425853808547517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800344851617235872365011 8700517277425853808547517)
          ·
            refine ⟨3262693979034695178205319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8700517277425853808547517 3262693979034695178205319)
            ·
              refine ⟨4894040968552042767307979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3262693979034695178205319 4894040968552042767307979)
              ·
                refine ⟨7341061452828064150961969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894040968552042767307979 7341061452828064150961969)
                ·
                  refine ⟨5505796089621048113221477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7341061452828064150961969 5505796089621048113221477)
                  ·
                    refine ⟨1032336766803946521229027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505796089621048113221477 1032336766803946521229027)
                    ·
                      rfl

theorem cell22_3015703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_3015703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015703 prefixEnd_3015703 := by exact prefixLift 3015703
  have htrace : WordTrace (prefixWord ++ tailWord_3015703) baseStart_3015703 baseEnd_3015703 := by
    simpa [prefixWord, tailWord_3015703, baseEnd_3015703] using wordTrace_append hprefix tailTrace_3015703
  have hstable : (prefixWord ++ tailWord_3015703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015703).length < 2 ^ (prefixWord ++ tailWord_3015703).sum := by decide
  have hdescent : baseEnd_3015703 < baseStart_3015703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015722 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3015722 : Nat := 118140960795 + 3015722 * 2 ^ 59
def prefixEnd_3015722 : Nat := 4983230072969 + 3 ^ 40 * 3015722 * 2
def baseEnd_3015722 : Nat := 1032343270892236805003969

theorem tailTrace_3015722 : CollatzResearch.WordTrace tailWord_3015722 prefixEnd_3015722 1032343270892236805003969 := by
  unfold tailWord_3015722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27498104395140428289484355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73328278387041142105291613 27498104395140428289484355)
  ·
    refine ⟨41247156592710642434226533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27498104395140428289484355 41247156592710642434226533)
    ·
      refine ⟨7733841861133245456417475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41247156592710642434226533 7733841861133245456417475)
      ·
        refine ⟨11600762791699868184626213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7733841861133245456417475 11600762791699868184626213)
        ·
          refine ⟨2175143023443725284617415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11600762791699868184626213 2175143023443725284617415)
          ·
            refine ⟨3262714535165587926926123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175143023443725284617415 3262714535165587926926123)
            ·
              refine ⟨4894071802748381890389185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3262714535165587926926123 4894071802748381890389185)
              ·
                refine ⟨3670553852061286417791889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4894071802748381890389185 3670553852061286417791889)
                ·
                  refine ⟨2752915389045964813343917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3670553852061286417791889 2752915389045964813343917)
                  ·
                    refine ⟨1032343270892236805003969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752915389045964813343917 1032343270892236805003969)
                    ·
                      rfl

theorem cell22_3015722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3015722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015722 prefixEnd_3015722 := by exact prefixLift 3015722
  have htrace : WordTrace (prefixWord ++ tailWord_3015722) baseStart_3015722 baseEnd_3015722 := by
    simpa [prefixWord, tailWord_3015722, baseEnd_3015722] using wordTrace_append hprefix tailTrace_3015722
  have hstable : (prefixWord ++ tailWord_3015722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015722).length < 2 ^ (prefixWord ++ tailWord_3015722).sum := by decide
  have hdescent : baseEnd_3015722 < baseStart_3015722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015729 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 7]
def baseStart_3015729 : Nat := 118140960795 + 3015729 * 2 ^ 59
def prefixEnd_3015729 : Nat := 4983230072969 + 3 ^ 40 * 3015729 * 2
def baseEnd_3015729 : Nat := 344115222378430373359649

theorem tailTrace_3015729 : CollatzResearch.WordTrace tailWord_3015729 prefixEnd_3015729 344115222378430373359649 := by
  unfold tailWord_3015729
  simp only [CollatzResearch.WordTrace]
  refine ⟨109992672891536353353442241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73328448594357568902294827 109992672891536353353442241)
  ·
    refine ⟨82494504668652265015081681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109992672891536353353442241 82494504668652265015081681)
    ·
      refine ⟨61870878501489198761311261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82494504668652265015081681 61870878501489198761311261)
      ·
        refine ⟨23201579438058449535491723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61870878501489198761311261 23201579438058449535491723)
        ·
          refine ⟨34802369157087674303237585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23201579438058449535491723 34802369157087674303237585)
          ·
            refine ⟨26101776867815755727428189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34802369157087674303237585 26101776867815755727428189)
            ·
              refine ⟨9788166325430908397785571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26101776867815755727428189 9788166325430908397785571)
              ·
                refine ⟨14682249488146362596678357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9788166325430908397785571 14682249488146362596678357)
                ·
                  refine ⟨344115222378430373359649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14682249488146362596678357 344115222378430373359649)
                  ·
                    rfl

theorem cell22_3015729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_3015729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015729 prefixEnd_3015729 := by exact prefixLift 3015729
  have htrace : WordTrace (prefixWord ++ tailWord_3015729) baseStart_3015729 baseEnd_3015729 := by
    simpa [prefixWord, tailWord_3015729, baseEnd_3015729] using wordTrace_append hprefix tailTrace_3015729
  have hstable : (prefixWord ++ tailWord_3015729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015729).length < 2 ^ (prefixWord ++ tailWord_3015729).sum := by decide
  have hdescent : baseEnd_3015729 < baseStart_3015729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015744 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_3015744 : Nat := 118140960795 + 3015744 * 2 ^ 59
def prefixEnd_3015744 : Nat := 4983230072969 + 3 ^ 40 * 3015744 * 2
def baseEnd_3015744 : Nat := 1032350801941836080953901

theorem tailTrace_3015744 : CollatzResearch.WordTrace tailWord_3015744 prefixEnd_3015744 1032350801941836080953901 := by
  unfold tailWord_3015744
  simp only [CollatzResearch.WordTrace]
  refine ⟨54996609993241005457619143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73328813324321340610158857 54996609993241005457619143)
  ·
    refine ⟨82494914989861508186428715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54996609993241005457619143 82494914989861508186428715)
    ·
      refine ⟨123742372484792262279643073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82494914989861508186428715 123742372484792262279643073)
      ·
        refine ⟨92806779363594196709732305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123742372484792262279643073 92806779363594196709732305)
        ·
          refine ⟨69605084522695647532299229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92806779363594196709732305 69605084522695647532299229)
          ·
            refine ⟨26101906696010867824612211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69605084522695647532299229 26101906696010867824612211)
            ·
              refine ⟨39152860044016301736918317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26101906696010867824612211 39152860044016301736918317)
              ·
                refine ⟨14682322516506113151344369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39152860044016301736918317 14682322516506113151344369)
                ·
                  refine ⟨11011741887379584863508277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14682322516506113151344369 11011741887379584863508277)
                  ·
                    refine ⟨1032350801941836080953901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11011741887379584863508277 1032350801941836080953901)
                    ·
                      rfl

theorem cell22_3015744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_3015744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015744 prefixEnd_3015744 := by exact prefixLift 3015744
  have htrace : WordTrace (prefixWord ++ tailWord_3015744) baseStart_3015744 baseEnd_3015744 := by
    simpa [prefixWord, tailWord_3015744, baseEnd_3015744] using wordTrace_append hprefix tailTrace_3015744
  have hstable : (prefixWord ++ tailWord_3015744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015744).length < 2 ^ (prefixWord ++ tailWord_3015744).sum := by decide
  have hdescent : baseEnd_3015744 < baseStart_3015744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015750 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3015750 : Nat := 118140960795 + 3015750 * 2 ^ 59
def prefixEnd_3015750 : Nat := 4983230072969 + 3 ^ 40 * 3015750 * 2
def baseEnd_3015750 : Nat := 1032352855864454065303883

theorem tailTrace_3015750 : CollatzResearch.WordTrace tailWord_3015750 prefixEnd_3015750 1032352855864454065303883 := by
  unfold tailWord_3015750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437294963264383560623647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73328959216306849293304469 3437294963264383560623647)
  ·
    refine ⟨5155942444896575340935471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3437294963264383560623647 5155942444896575340935471)
    ·
      refine ⟨7733913667344863011403207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5155942444896575340935471 7733913667344863011403207)
      ·
        refine ⟨11600870501017294517104811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7733913667344863011403207 11600870501017294517104811)
        ·
          refine ⟨17401305751525941775657217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11600870501017294517104811 17401305751525941775657217)
          ·
            refine ⟨13050979313644456331742913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17401305751525941775657217 13050979313644456331742913)
            ·
              refine ⟨9788234485233342248807185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13050979313644456331742913 9788234485233342248807185)
              ·
                refine ⟨7341175863925006686605389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9788234485233342248807185 7341175863925006686605389)
                ·
                  refine ⟨2752940948971877507477021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7341175863925006686605389 2752940948971877507477021)
                  ·
                    refine ⟨1032352855864454065303883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752940948971877507477021 1032352855864454065303883)
                    ·
                      rfl

theorem cell22_3015750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3015750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015750 prefixEnd_3015750 := by exact prefixLift 3015750
  have htrace : WordTrace (prefixWord ++ tailWord_3015750) baseStart_3015750 baseEnd_3015750 := by
    simpa [prefixWord, tailWord_3015750, baseEnd_3015750] using wordTrace_append hprefix tailTrace_3015750
  have hstable : (prefixWord ++ tailWord_3015750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015750).length < 2 ^ (prefixWord ++ tailWord_3015750).sum := by decide
  have hdescent : baseEnd_3015750 < baseStart_3015750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015776 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_3015776 : Nat := 118140960795 + 3015776 * 2 ^ 59
def prefixEnd_3015776 : Nat := 4983230072969 + 3 ^ 40 * 3015776 * 2
def baseEnd_3015776 : Nat := 1032361756195798664153803

theorem tailTrace_3015776 : CollatzResearch.WordTrace tailWord_3015776 prefixEnd_3015776 1032361756195798664153803 := by
  unfold tailWord_3015776
  simp only [CollatzResearch.WordTrace]
  refine ⟨54997193561183040190201591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73329591414910720253602121 54997193561183040190201591)
  ·
    refine ⟨82495790341774560285302387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54997193561183040190201591 82495790341774560285302387)
    ·
      refine ⟨123743685512661840427953581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82495790341774560285302387 123743685512661840427953581)
      ·
        refine ⟨46403882067248190160482593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123743685512661840427953581 46403882067248190160482593)
        ·
          refine ⟨34802911550436142620361945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46403882067248190160482593 34802911550436142620361945)
          ·
            refine ⟨26102183662827106965271459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34802911550436142620361945 26102183662827106965271459)
            ·
              refine ⟨39153275494240660447907189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26102183662827106965271459 39153275494240660447907189)
              ·
                refine ⟨3670619577585061916991299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39153275494240660447907189 3670619577585061916991299)
                ·
                  refine ⟨5505929366377592875486949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670619577585061916991299 5505929366377592875486949)
                  ·
                    refine ⟨1032361756195798664153803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505929366377592875486949 1032361756195798664153803)
                    ·
                      rfl

theorem cell22_3015776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_3015776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015776 prefixEnd_3015776 := by exact prefixLift 3015776
  have htrace : WordTrace (prefixWord ++ tailWord_3015776) baseStart_3015776 baseEnd_3015776 := by
    simpa [prefixWord, tailWord_3015776, baseEnd_3015776] using wordTrace_append hprefix tailTrace_3015776
  have hstable : (prefixWord ++ tailWord_3015776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015776).length < 2 ^ (prefixWord ++ tailWord_3015776).sum := by decide
  have hdescent : baseEnd_3015776 < baseStart_3015776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015784 : List Nat := [2, 1, 4, 4, 1, 1, 3, 2, 1, 3]
def baseStart_3015784 : Nat := 118140960795 + 3015784 * 2 ^ 59
def prefixEnd_3015784 : Nat := 4983230072969 + 3 ^ 40 * 3015784 * 2
def baseEnd_3015784 : Nat := 1032364494759289309953779

theorem tailTrace_3015784 : CollatzResearch.WordTrace tailWord_3015784 prefixEnd_3015784 1032364494759289309953779 := by
  unfold tailWord_3015784
  simp only [CollatzResearch.WordTrace]
  refine ⟨54997339453168548873347203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73329785937558065164462937 54997339453168548873347203)
  ·
    refine ⟨82496009179752823310020805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54997339453168548873347203 82496009179752823310020805)
    ·
      refine ⟨15468001721203654370628901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82496009179752823310020805 15468001721203654370628901)
      ·
        refine ⟨2900250322725685194492919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15468001721203654370628901 2900250322725685194492919)
        ·
          refine ⟨4350375484088527791739379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2900250322725685194492919 4350375484088527791739379)
          ·
            refine ⟨6525563226132791687609069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350375484088527791739379 6525563226132791687609069)
            ·
              refine ⟨2447086209799796882853401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6525563226132791687609069 2447086209799796882853401)
              ·
                refine ⟨1835314657349847662140051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447086209799796882853401 1835314657349847662140051)
                ·
                  refine ⟨2752971986024771493210077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835314657349847662140051 2752971986024771493210077)
                  ·
                    refine ⟨1032364494759289309953779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752971986024771493210077 1032364494759289309953779)
                    ·
                      rfl

theorem cell22_3015784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_3015784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015784 prefixEnd_3015784 := by exact prefixLift 3015784
  have htrace : WordTrace (prefixWord ++ tailWord_3015784) baseStart_3015784 baseEnd_3015784 := by
    simpa [prefixWord, tailWord_3015784, baseEnd_3015784] using wordTrace_append hprefix tailTrace_3015784
  have hstable : (prefixWord ++ tailWord_3015784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015784).length < 2 ^ (prefixWord ++ tailWord_3015784).sum := by decide
  have hdescent : baseEnd_3015784 < baseStart_3015784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015797 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 5]
def baseStart_3015797 : Nat := 118140960795 + 3015797 * 2 ^ 59
def prefixEnd_3015797 : Nat := 4983230072969 + 3 ^ 40 * 3015797 * 2
def baseEnd_3015797 : Nat := 344122981641653869792913

theorem tailTrace_3015797 : CollatzResearch.WordTrace tailWord_3015797 prefixEnd_3015797 344122981641653869792913 := by
  unfold tailWord_3015797
  simp only [CollatzResearch.WordTrace]
  refine ⟨109995153055290000966917645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73330102036860000644611763 109995153055290000966917645)
  ·
    refine ⟨41248182395733750362594117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109995153055290000966917645 41248182395733750362594117)
    ·
      refine ⟨7734034199200078192986397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41248182395733750362594117 7734034199200078192986397)
      ·
        refine ⟨2900262824700029322369899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7734034199200078192986397 2900262824700029322369899)
        ·
          refine ⟨4350394237050043983554849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2900262824700029322369899 4350394237050043983554849)
          ·
            refine ⟨3262795677787532987666137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4350394237050043983554849 3262795677787532987666137)
            ·
              refine ⟨2447096758340649740749603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3262795677787532987666137 2447096758340649740749603)
              ·
                refine ⟨3670645137510974611124405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447096758340649740749603 3670645137510974611124405)
                ·
                  refine ⟨344122981641653869792913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3670645137510974611124405 344122981641653869792913)
                  ·
                    rfl

theorem cell22_3015797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_3015797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015797 prefixEnd_3015797 := by exact prefixLift 3015797
  have htrace : WordTrace (prefixWord ++ tailWord_3015797) baseStart_3015797 baseEnd_3015797 := by
    simpa [prefixWord, tailWord_3015797, baseEnd_3015797] using wordTrace_append hprefix tailTrace_3015797
  have hstable : (prefixWord ++ tailWord_3015797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015797).length < 2 ^ (prefixWord ++ tailWord_3015797).sum := by decide
  have hdescent : baseEnd_3015797 < baseStart_3015797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015868 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_3015868 : Nat := 118140960795 + 3015868 * 2 ^ 59
def prefixEnd_3015868 : Nat := 4983230072969 + 3 ^ 40 * 3015868 * 2
def baseEnd_3015868 : Nat := 1032393249675941090853521

theorem tailTrace_3015868 : CollatzResearch.WordTrace tailWord_3015868 prefixEnd_3015868 1032393249675941090853521 := by
  unfold tailWord_3015868
  simp only [CollatzResearch.WordTrace]
  refine ⟨54998871319016390046376129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73331828425355186728501505 54998871319016390046376129)
  ·
    refine ⟨41249153489262292534782097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54998871319016390046376129 41249153489262292534782097)
    ·
      refine ⟨30936865116946719401086573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41249153489262292534782097 30936865116946719401086573)
      ·
        refine ⟨11601324418855019775407465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30936865116946719401086573 11601324418855019775407465)
        ·
          refine ⟨8700993314141264831555599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11601324418855019775407465 8700993314141264831555599)
          ·
            refine ⟨13051489971211897247333399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700993314141264831555599 13051489971211897247333399)
            ·
              refine ⟨19577234956817845871000099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13051489971211897247333399 19577234956817845871000099)
              ·
                refine ⟨29365852435226768806500149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19577234956817845871000099 29365852435226768806500149)
                ·
                  refine ⟨2753048665802509575609389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29365852435226768806500149 2753048665802509575609389)
                  ·
                    refine ⟨1032393249675941090853521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2753048665802509575609389 1032393249675941090853521)
                    ·
                      rfl

theorem cell22_3015868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_3015868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015868 prefixEnd_3015868 := by exact prefixLift 3015868
  have htrace : WordTrace (prefixWord ++ tailWord_3015868) baseStart_3015868 baseEnd_3015868 := by
    simpa [prefixWord, tailWord_3015868, baseEnd_3015868] using wordTrace_append hprefix tailTrace_3015868
  have hstable : (prefixWord ++ tailWord_3015868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015868).length < 2 ^ (prefixWord ++ tailWord_3015868).sum := by decide
  have hdescent : baseEnd_3015868 < baseStart_3015868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015878 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3015878 : Nat := 118140960795 + 3015878 * 2 ^ 59
def prefixEnd_3015878 : Nat := 4983230072969 + 3 ^ 40 * 3015878 * 2
def baseEnd_3015878 : Nat := 1032396672880304398103491

theorem tailTrace_3015878 : CollatzResearch.WordTrace tailWord_3015878 prefixEnd_3015878 1032396672880304398103491 := by
  unfold tailWord_3015878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437440855249892243769259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73332071578664367867077525 3437440855249892243769259)
  ·
    refine ⟨5156161282874838365653889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3437440855249892243769259 5156161282874838365653889)
    ·
      refine ⟨3867120962156128774240417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5156161282874838365653889 3867120962156128774240417)
      ·
        refine ⟨2900340721617096580680313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3867120962156128774240417 2900340721617096580680313)
        ·
          refine ⟨2175255541212822435510235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2900340721617096580680313 2175255541212822435510235)
          ·
            refine ⟨3262883311819233653265353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175255541212822435510235 3262883311819233653265353)
            ·
              refine ⟨2447162483864425239949015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3262883311819233653265353 2447162483864425239949015)
              ·
                refine ⟨3670743725796637859923523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447162483864425239949015 3670743725796637859923523)
                ·
                  refine ⟨5506115588694956789885285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670743725796637859923523 5506115588694956789885285)
                  ·
                    refine ⟨1032396672880304398103491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5506115588694956789885285 1032396672880304398103491)
                    ·
                      rfl

theorem cell22_3015878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3015878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015878 prefixEnd_3015878 := by exact prefixLift 3015878
  have htrace : WordTrace (prefixWord ++ tailWord_3015878) baseStart_3015878 baseEnd_3015878 := by
    simpa [prefixWord, tailWord_3015878, baseEnd_3015878] using wordTrace_append hprefix tailTrace_3015878
  have hstable : (prefixWord ++ tailWord_3015878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015878).length < 2 ^ (prefixWord ++ tailWord_3015878).sum := by decide
  have hdescent : baseEnd_3015878 < baseStart_3015878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015941 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_3015941 : Nat := 118140960795 + 3015941 * 2 ^ 59
def prefixEnd_3015941 : Nat := 4983230072969 + 3 ^ 40 * 3015941 * 2
def baseEnd_3015941 : Nat := 1032418239067793233778297

theorem tailTrace_3015941 : CollatzResearch.WordTrace tailWord_3015941 prefixEnd_3015941 1032418239067793233778297 := by
  unfold tailWord_3015941
  simp only [CollatzResearch.WordTrace]
  refine ⟨110000405166768313560159677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73333603444512209040106451 110000405166768313560159677)
  ·
    refine ⟨41250151937538117585059879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110000405166768313560159677 41250151937538117585059879)
    ·
      refine ⟨61875227906307176377589819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41250151937538117585059879 61875227906307176377589819)
      ·
        refine ⟨92812841859460764566384729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61875227906307176377589819 92812841859460764566384729)
        ·
          refine ⟨69609631394595573424788547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92812841859460764566384729 69609631394595573424788547)
          ·
            refine ⟨104414447091893360137182821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69609631394595573424788547 104414447091893360137182821)
            ·
              refine ⟨19577708829730005025721779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104414447091893360137182821 19577708829730005025721779)
              ·
                refine ⟨29366563244595007538582669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19577708829730005025721779 29366563244595007538582669)
                ·
                  refine ⟨11012461216723127826968501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29366563244595007538582669 11012461216723127826968501)
                  ·
                    refine ⟨1032418239067793233778297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11012461216723127826968501 1032418239067793233778297)
                    ·
                      rfl

theorem cell22_3015941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_3015941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015941 prefixEnd_3015941 := by exact prefixLift 3015941
  have htrace : WordTrace (prefixWord ++ tailWord_3015941) baseStart_3015941 baseEnd_3015941 := by
    simpa [prefixWord, tailWord_3015941, baseEnd_3015941] using wordTrace_append hprefix tailTrace_3015941
  have hstable : (prefixWord ++ tailWord_3015941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015941).length < 2 ^ (prefixWord ++ tailWord_3015941).sum := by decide
  have hdescent : baseEnd_3015941 < baseStart_3015941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015966 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_3015966 : Nat := 118140960795 + 3015966 * 2 ^ 59
def prefixEnd_3015966 : Nat := 4983230072969 + 3 ^ 40 * 3015966 * 2
def baseEnd_3015966 : Nat := 344142265692900500634407

theorem tailTrace_3015966 : CollatzResearch.WordTrace tailWord_3015966 prefixEnd_3015966 344142265692900500634407 := by
  unfold tailWord_3015966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13750164623959717853727469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73334211327785161886546501 13750164623959717853727469)
  ·
    refine ⟨5156311733984894195147801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13750164623959717853727469 5156311733984894195147801)
    ·
      refine ⟨3867233800488670646360851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5156311733984894195147801 3867233800488670646360851)
      ·
        refine ⟨5800850700733005969541277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3867233800488670646360851 5800850700733005969541277)
        ·
          refine ⟨2175319012774877238577979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5800850700733005969541277 2175319012774877238577979)
          ·
            refine ⟨3262978519162315857866969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175319012774877238577979 3262978519162315857866969)
            ·
              refine ⟨2447233889371736893400227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3262978519162315857866969 2447233889371736893400227)
              ·
                refine ⟨3670850834057605340100341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447233889371736893400227 3670850834057605340100341)
                ·
                  refine ⟨344142265692900500634407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3670850834057605340100341 344142265692900500634407)
                  ·
                    rfl

theorem cell22_3015966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_3015966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015966 prefixEnd_3015966 := by exact prefixLift 3015966
  have htrace : WordTrace (prefixWord ++ tailWord_3015966) baseStart_3015966 baseEnd_3015966 := by
    simpa [prefixWord, tailWord_3015966, baseEnd_3015966] using wordTrace_append hprefix tailTrace_3015966
  have hstable : (prefixWord ++ tailWord_3015966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015966).length < 2 ^ (prefixWord ++ tailWord_3015966).sum := by decide
  have hdescent : baseEnd_3015966 < baseStart_3015966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015971 : List Nat := [1, 1, 1, 4, 2, 3, 1, 9]
def baseStart_3015971 : Nat := 118140960795 + 3015971 * 2 ^ 59
def prefixEnd_3015971 : Nat := 4983230072969 + 3 ^ 40 * 3015971 * 2
def baseEnd_3015971 : Nat := 114714278742320350614245

theorem tailTrace_3015971 : CollatzResearch.WordTrace tailWord_3015971 prefixEnd_3015971 114714278742320350614245 := by
  unfold tailWord_3015971
  simp only [CollatzResearch.WordTrace]
  refine ⟨110001499356659628683751767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73334332904439752455834511 110001499356659628683751767)
  ·
    refine ⟨165002249034989443025627651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110001499356659628683751767 165002249034989443025627651)
    ·
      refine ⟨247503373552484164538441477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165002249034989443025627651 247503373552484164538441477)
      ·
        refine ⟨46406882541090780850957777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247503373552484164538441477 46406882541090780850957777)
        ·
          refine ⟨34805161905818085638218333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46406882541090780850957777 34805161905818085638218333)
          ·
            refine ⟨13051935714681782114331875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34805161905818085638218333 13051935714681782114331875)
            ·
              refine ⟨19577903572022673171497813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13051935714681782114331875 19577903572022673171497813)
              ·
                refine ⟨114714278742320350614245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19577903572022673171497813 114714278742320350614245)
                ·
                  rfl

theorem cell22_3015971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 9].length) (baseStart_3015971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015971 prefixEnd_3015971 := by exact prefixLift 3015971
  have htrace : WordTrace (prefixWord ++ tailWord_3015971) baseStart_3015971 baseEnd_3015971 := by
    simpa [prefixWord, tailWord_3015971, baseEnd_3015971] using wordTrace_append hprefix tailTrace_3015971
  have hstable : (prefixWord ++ tailWord_3015971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015971).length < 2 ^ (prefixWord ++ tailWord_3015971).sum := by decide
  have hdescent : baseEnd_3015971 < baseStart_3015971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015988 : List Nat := [2, 5, 1, 1, 1, 1, 1, 10]
def baseStart_3015988 : Nat := 118140960795 + 3015988 * 2 ^ 59
def prefixEnd_3015988 : Nat := 4983230072969 + 3 ^ 40 * 3015988 * 2
def baseEnd_3015988 : Nat := 114714925347588975317017

theorem tailTrace_3015988 : CollatzResearch.WordTrace tailWord_3015988 prefixEnd_3015988 114714925347588975317017 := by
  unfold tailWord_3015988
  simp only [CollatzResearch.WordTrace]
  refine ⟨55001059698799020293560309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73334746265065360391413745 55001059698799020293560309)
  ·
    refine ⟨5156349346762408152521279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55001059698799020293560309 5156349346762408152521279)
    ·
      refine ⟨7734524020143612228781919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5156349346762408152521279 7734524020143612228781919)
      ·
        refine ⟨11601786030215418343172879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7734524020143612228781919 11601786030215418343172879)
        ·
          refine ⟨17402679045323127514759319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11601786030215418343172879 17402679045323127514759319)
          ·
            refine ⟨26104018567984691272138979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17402679045323127514759319 26104018567984691272138979)
            ·
              refine ⟨39156027851977036908208469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26104018567984691272138979 39156027851977036908208469)
              ·
                refine ⟨114714925347588975317017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39156027851977036908208469 114714925347588975317017)
                ·
                  rfl

theorem cell22_3015988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 10].length) (baseStart_3015988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3015988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3015988 prefixEnd_3015988 := by exact prefixLift 3015988
  have htrace : WordTrace (prefixWord ++ tailWord_3015988) baseStart_3015988 baseEnd_3015988 := by
    simpa [prefixWord, tailWord_3015988, baseEnd_3015988] using wordTrace_append hprefix tailTrace_3015988
  have hstable : (prefixWord ++ tailWord_3015988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015988).length < 2 ^ (prefixWord ++ tailWord_3015988).sum := by decide
  have hdescent : baseEnd_3015988 < baseStart_3015988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016020 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3016020 : Nat := 118140960795 + 3016020 * 2 ^ 59
def prefixEnd_3016020 : Nat := 4983230072969 + 3 ^ 40 * 3016020 * 2
def baseEnd_3016020 : Nat := 1032445282382263361053055

theorem tailTrace_3016020 : CollatzResearch.WordTrace tailWord_3016020 prefixEnd_3016020 1032445282382263361053055 := by
  unfold tailWord_3016020
  simp only [CollatzResearch.WordTrace]
  refine ⟨55001643266741055026142757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73335524355654740034857009 55001643266741055026142757)
  ·
    refine ⟨10312808112513947817401767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55001643266741055026142757 10312808112513947817401767)
    ·
      refine ⟨15469212168770921726102651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10312808112513947817401767 15469212168770921726102651)
      ·
        refine ⟨23203818253156382589153977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15469212168770921726102651 23203818253156382589153977)
        ·
          refine ⟨17402863689867286941865483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23203818253156382589153977 17402863689867286941865483)
          ·
            refine ⟨26104295534800930412798225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17402863689867286941865483 26104295534800930412798225)
            ·
              refine ⟨19578221651100697809598669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26104295534800930412798225 19578221651100697809598669)
              ·
                refine ⟨7341833119162761678599501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19578221651100697809598669 7341833119162761678599501)
                ·
                  refine ⟨2753187419686035629474813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7341833119162761678599501 2753187419686035629474813)
                  ·
                    refine ⟨1032445282382263361053055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2753187419686035629474813 1032445282382263361053055)
                    ·
                      rfl

theorem cell22_3016020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3016020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016020 prefixEnd_3016020 := by exact prefixLift 3016020
  have htrace : WordTrace (prefixWord ++ tailWord_3016020) baseStart_3016020 baseEnd_3016020 := by
    simpa [prefixWord, tailWord_3016020, baseEnd_3016020] using wordTrace_append hprefix tailTrace_3016020
  have hstable : (prefixWord ++ tailWord_3016020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016020).length < 2 ^ (prefixWord ++ tailWord_3016020).sum := by decide
  have hdescent : baseEnd_3016020 < baseStart_3016020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016108 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_3016108 : Nat := 118140960795 + 3016108 * 2 ^ 59
def prefixEnd_3016108 : Nat := 4983230072969 + 3 ^ 40 * 3016108 * 2
def baseEnd_3016108 : Nat := 1032475406580660464852785

theorem tailTrace_3016108 : CollatzResearch.WordTrace tailWord_3016108 prefixEnd_3016108 1032475406580660464852785 := by
  unfold tailWord_3016108
  simp only [CollatzResearch.WordTrace]
  refine ⟨55003248078581650540744489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73337664104775534054325985 55003248078581650540744489)
  ·
    refine ⟨41252436058936237905558367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55003248078581650540744489 41252436058936237905558367)
    ·
      refine ⟨61878654088404356858337551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41252436058936237905558367 61878654088404356858337551)
      ·
        refine ⟨92817981132606535287506327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61878654088404356858337551 92817981132606535287506327)
        ·
          refine ⟨139226971698909802931259491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92817981132606535287506327 139226971698909802931259491)
          ·
            refine ⟨208840457548364704396889237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139226971698909802931259491 208840457548364704396889237)
            ·
              refine ⟨9789396447579595518604183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208840457548364704396889237 9789396447579595518604183)
              ·
                refine ⟨14684094671369393277906275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9789396447579595518604183 14684094671369393277906275)
                ·
                  refine ⟨22026142007054089916859413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14684094671369393277906275 22026142007054089916859413)
                  ·
                    refine ⟨1032475406580660464852785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22026142007054089916859413 1032475406580660464852785)
                    ·
                      rfl

theorem cell22_3016108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_3016108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016108 prefixEnd_3016108 := by exact prefixLift 3016108
  have htrace : WordTrace (prefixWord ++ tailWord_3016108) baseStart_3016108 baseEnd_3016108 := by
    simpa [prefixWord, tailWord_3016108, baseEnd_3016108] using wordTrace_append hprefix tailTrace_3016108
  have hstable : (prefixWord ++ tailWord_3016108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016108).length < 2 ^ (prefixWord ++ tailWord_3016108).sum := by decide
  have hdescent : baseEnd_3016108 < baseStart_3016108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016125 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_3016125 : Nat := 118140960795 + 3016125 * 2 ^ 59
def prefixEnd_3016125 : Nat := 4983230072969 + 3 ^ 40 * 3016125 * 2
def baseEnd_3016125 : Nat := 1032481226028078087177733

theorem tailTrace_3016125 : CollatzResearch.WordTrace tailWord_3016125 prefixEnd_3016125 1032481226028078087177733 := by
  unfold tailWord_3016125
  simp only [CollatzResearch.WordTrace]
  refine ⟨110007116198101712984857829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73338077465401141989905219 110007116198101712984857829)
  ·
    refine ⟨20626334287144071184660843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110007116198101712984857829 20626334287144071184660843)
    ·
      refine ⟨30939501430716106776991265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20626334287144071184660843 30939501430716106776991265)
      ·
        refine ⟨23204626073037080082743449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30939501430716106776991265 23204626073037080082743449)
        ·
          refine ⟨17403469554777810062057587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23204626073037080082743449 17403469554777810062057587)
          ·
            refine ⟨26105204332166715093086381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17403469554777810062057587 26105204332166715093086381)
            ·
              refine ⟨9789451624562518159907393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26105204332166715093086381 9789451624562518159907393)
              ·
                refine ⟨7342088718421888619930545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9789451624562518159907393 7342088718421888619930545)
                ·
                  refine ⟨5506566538816416464947909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7342088718421888619930545 5506566538816416464947909)
                  ·
                    refine ⟨1032481226028078087177733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5506566538816416464947909 1032481226028078087177733)
                    ·
                      rfl

theorem cell22_3016125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_3016125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016125 prefixEnd_3016125 := by exact prefixLift 3016125
  have htrace : WordTrace (prefixWord ++ tailWord_3016125) baseStart_3016125 baseEnd_3016125 := by
    simpa [prefixWord, tailWord_3016125, baseEnd_3016125] using wordTrace_append hprefix tailTrace_3016125
  have hstable : (prefixWord ++ tailWord_3016125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016125).length < 2 ^ (prefixWord ++ tailWord_3016125).sum := by decide
  have hdescent : baseEnd_3016125 < baseStart_3016125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016140 : List Nat := [2, 2, 1, 4, 2, 2, 2, 7]
def baseStart_3016140 : Nat := 118140960795 + 3016140 * 2 ^ 59
def prefixEnd_3016140 : Nat := 4983230072969 + 3 ^ 40 * 3016140 * 2
def baseEnd_3016140 : Nat := 114720706759402560894743

theorem tailTrace_3016140 : CollatzResearch.WordTrace tailWord_3016140 prefixEnd_3016140 114720706759402560894743 := by
  unfold tailWord_3016140
  simp only [CollatzResearch.WordTrace]
  refine ⟨55003831646523685273326937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73338442195364913697769249 55003831646523685273326937)
  ·
    refine ⟨41252873734892763954995203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55003831646523685273326937 41252873734892763954995203)
    ·
      refine ⟨61879310602339145932492805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41252873734892763954995203 61879310602339145932492805)
      ·
        refine ⟨11602370737938589862342401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61879310602339145932492805 11602370737938589862342401)
        ·
          refine ⟨8701778053453942396756801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11602370737938589862342401 8701778053453942396756801)
          ·
            refine ⟨6526333540090456797567601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8701778053453942396756801 6526333540090456797567601)
            ·
              refine ⟨4894750155067842598175701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6526333540090456797567601 4894750155067842598175701)
              ·
                refine ⟨114720706759402560894743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4894750155067842598175701 114720706759402560894743)
                ·
                  rfl

theorem cell22_3016140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 7].length) (baseStart_3016140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016140 prefixEnd_3016140 := by exact prefixLift 3016140
  have htrace : WordTrace (prefixWord ++ tailWord_3016140) baseStart_3016140 baseEnd_3016140 := by
    simpa [prefixWord, tailWord_3016140, baseEnd_3016140] using wordTrace_append hprefix tailTrace_3016140
  have hstable : (prefixWord ++ tailWord_3016140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016140).length < 2 ^ (prefixWord ++ tailWord_3016140).sum := by decide
  have hdescent : baseEnd_3016140 < baseStart_3016140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016189 : List Nat := [1, 4, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_3016189 : Nat := 118140960795 + 3016189 * 2 ^ 59
def prefixEnd_3016189 : Nat := 4983230072969 + 3 ^ 40 * 3016189 * 2
def baseEnd_3016189 : Nat := 1032503134536003253577537

theorem tailTrace_3016189 : CollatzResearch.WordTrace tailWord_3016189 prefixEnd_3016189 1032503134536003253577537 := by
  unfold tailWord_3016189
  simp only [CollatzResearch.WordTrace]
  refine ⟨110009450469869851915187621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73339633646579901276791747 110009450469869851915187621)
  ·
    refine ⟨20626771963100597234097679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110009450469869851915187621 20626771963100597234097679)
    ·
      refine ⟨30940157944650895851146519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20626771963100597234097679 30940157944650895851146519)
      ·
        refine ⟨46410236916976343776719779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30940157944650895851146519 46410236916976343776719779)
        ·
          refine ⟨69615355375464515665079669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46410236916976343776719779 69615355375464515665079669)
          ·
            refine ⟨6526439566449798343601219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69615355375464515665079669 6526439566449798343601219)
            ·
              refine ⟨9789659349674697515401829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6526439566449798343601219 9789659349674697515401829)
              ·
                refine ⟨1835561128064005784137843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9789659349674697515401829 1835561128064005784137843)
                ·
                  refine ⟨2753341692096008676206765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835561128064005784137843 2753341692096008676206765)
                  ·
                    refine ⟨1032503134536003253577537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2753341692096008676206765 1032503134536003253577537)
                    ·
                      rfl

theorem cell22_3016189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_3016189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016189 prefixEnd_3016189 := by exact prefixLift 3016189
  have htrace : WordTrace (prefixWord ++ tailWord_3016189) baseStart_3016189 baseEnd_3016189 := by
    simpa [prefixWord, tailWord_3016189, baseEnd_3016189] using wordTrace_append hprefix tailTrace_3016189
  have hstable : (prefixWord ++ tailWord_3016189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016189).length < 2 ^ (prefixWord ++ tailWord_3016189).sum := by decide
  have hdescent : baseEnd_3016189 < baseStart_3016189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016247 : List Nat := [1, 1, 3, 1, 2, 4, 2, 4, 4]
def baseStart_3016247 : Nat := 118140960795 + 3016247 * 2 ^ 59
def prefixEnd_3016247 : Nat := 4983230072969 + 3 ^ 40 * 3016247 * 2
def baseEnd_3016247 : Nat := 344174329707103478542453

theorem tailTrace_3016247 : CollatzResearch.WordTrace tailWord_3016247 prefixEnd_3016247 344174329707103478542453 := by
  unfold tailWord_3016247
  simp only [CollatzResearch.WordTrace]
  refine ⟨110011565903659727820798995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73341043935773151880532663 110011565903659727820798995)
  ·
    refine ⟨165017348855489591731198493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110011565903659727820798995 165017348855489591731198493)
    ·
      refine ⟨61881505820808596899199435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165017348855489591731198493 61881505820808596899199435)
      ·
        refine ⟨92822258731212895348799153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61881505820808596899199435 92822258731212895348799153)
        ·
          refine ⟨69616694048409671511599365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92822258731212895348799153 69616694048409671511599365)
          ·
            refine ⟨13053130134076813408424881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69616694048409671511599365 13053130134076813408424881)
            ·
              refine ⟨9789847600557610056318661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13053130134076813408424881 9789847600557610056318661)
              ·
                refine ⟨1835596425104551885559749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9789847600557610056318661 1835596425104551885559749)
                ·
                  refine ⟨344174329707103478542453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1835596425104551885559749 344174329707103478542453)
                  ·
                    rfl

theorem cell22_3016247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 4].length) (baseStart_3016247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016247 prefixEnd_3016247 := by exact prefixLift 3016247
  have htrace : WordTrace (prefixWord ++ tailWord_3016247) baseStart_3016247 baseEnd_3016247 := by
    simpa [prefixWord, tailWord_3016247, baseEnd_3016247] using wordTrace_append hprefix tailTrace_3016247
  have hstable : (prefixWord ++ tailWord_3016247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016247).length < 2 ^ (prefixWord ++ tailWord_3016247).sum := by decide
  have hdescent : baseEnd_3016247 < baseStart_3016247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016382 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_3016382 : Nat := 118140960795 + 3016382 * 2 ^ 59
def prefixEnd_3016382 : Nat := 4983230072969 + 3 ^ 40 * 3016382 * 2
def baseEnd_3016382 : Nat := 344189734126738361167315

theorem tailTrace_3016382 : CollatzResearch.WordTrace tailWord_3016382 prefixEnd_3016382 344189734126738361167315 := by
  unfold tailWord_3016382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13752061219771330734620425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73344326505447097251308933 13752061219771330734620425)
  ·
    refine ⟨10314045914828498050965319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13752061219771330734620425 10314045914828498050965319)
    ·
      refine ⟨15471068872242747076447979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10314045914828498050965319 15471068872242747076447979)
      ·
        refine ⟨23206603308364120614671969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15471068872242747076447979 23206603308364120614671969)
        ·
          refine ⟨17404952481273090461003977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23206603308364120614671969 17404952481273090461003977)
          ·
            refine ⟨13053714360954817845752983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17404952481273090461003977 13053714360954817845752983)
            ·
              refine ⟨19580571541432226768629475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13053714360954817845752983 19580571541432226768629475)
              ·
                refine ⟨29370857312148340152944213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19580571541432226768629475 29370857312148340152944213)
                ·
                  refine ⟨344189734126738361167315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29370857312148340152944213 344189734126738361167315)
                  ·
                    rfl

theorem cell22_3016382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3016382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016382 prefixEnd_3016382 := by exact prefixLift 3016382
  have htrace : WordTrace (prefixWord ++ tailWord_3016382) baseStart_3016382 baseEnd_3016382 := by
    simpa [prefixWord, tailWord_3016382, baseEnd_3016382] using wordTrace_append hprefix tailTrace_3016382
  have hstable : (prefixWord ++ tailWord_3016382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016382).length < 2 ^ (prefixWord ++ tailWord_3016382).sum := by decide
  have hdescent : baseEnd_3016382 < baseStart_3016382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016401 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 1, 4]
def baseStart_3016401 : Nat := 118140960795 + 3016401 * 2 ^ 59
def prefixEnd_3016401 : Nat := 4983230072969 + 3 ^ 40 * 3016401 * 2
def baseEnd_3016401 : Nat := 1032575706468505367276887

theorem tailTrace_3016401 : CollatzResearch.WordTrace tailWord_3016401 prefixEnd_3016401 1032575706468505367276887 := by
  unfold tailWord_3016401
  simp only [CollatzResearch.WordTrace]
  refine ⟨110017182745101812121905057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73344788496734541414603371 110017182745101812121905057)
  ·
    refine ⟨82512887058826359091428793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110017182745101812121905057 82512887058826359091428793)
    ·
      refine ⟨61884665294119769318571595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82512887058826359091428793 61884665294119769318571595)
      ·
        refine ⟨92826997941179653977857393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61884665294119769318571595 92826997941179653977857393)
        ·
          refine ⟨69620248455884740483393045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92826997941179653977857393 69620248455884740483393045)
          ·
            refine ⟨3263449146369597210159049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69620248455884740483393045 3263449146369597210159049)
            ·
              refine ⟨2447586859777197907619287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3263449146369597210159049 2447586859777197907619287)
              ·
                refine ⟨3671380289665796861428931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447586859777197907619287 3671380289665796861428931)
                ·
                  refine ⟨5507070434498695292143397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671380289665796861428931 5507070434498695292143397)
                  ·
                    refine ⟨1032575706468505367276887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507070434498695292143397 1032575706468505367276887)
                    ·
                      rfl

theorem cell22_3016401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_3016401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016401 prefixEnd_3016401 := by exact prefixLift 3016401
  have htrace : WordTrace (prefixWord ++ tailWord_3016401) baseStart_3016401 baseEnd_3016401 := by
    simpa [prefixWord, tailWord_3016401, baseEnd_3016401] using wordTrace_append hprefix tailTrace_3016401
  have hstable : (prefixWord ++ tailWord_3016401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016401).length < 2 ^ (prefixWord ++ tailWord_3016401).sum := by decide
  have hdescent : baseEnd_3016401 < baseStart_3016401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016431 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 2, 3]
def baseStart_3016431 : Nat := 118140960795 + 3016431 * 2 ^ 59
def prefixEnd_3016431 : Nat := 4983230072969 + 3 ^ 40 * 3016431 * 2
def baseEnd_3016431 : Nat := 1032585976081595289026795

theorem tailTrace_3016431 : CollatzResearch.WordTrace tailWord_3016431 prefixEnd_3016431 1032585976081595289026795 := by
  unfold tailWord_3016431
  simp only [CollatzResearch.WordTrace]
  refine ⟨110018276934993127245497147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73345517956662084830331431 110018276934993127245497147)
  ·
    refine ⟨165027415402489690868245721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110018276934993127245497147 165027415402489690868245721)
    ·
      refine ⟨123770561551867268151184291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165027415402489690868245721 123770561551867268151184291)
      ·
        refine ⟨185655842327800902226776437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123770561551867268151184291 185655842327800902226776437)
        ·
          refine ⟨17405235218231334583760291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185655842327800902226776437 17405235218231334583760291)
          ·
            refine ⟨26107852827347001875640437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17405235218231334583760291 26107852827347001875640437)
            ·
              refine ⟨2447611202563781425841291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26107852827347001875640437 2447611202563781425841291)
              ·
                refine ⟨3671416803845672138761937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447611202563781425841291 3671416803845672138761937)
                ·
                  refine ⟨2753562602884254104071453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3671416803845672138761937 2753562602884254104071453)
                  ·
                    refine ⟨1032585976081595289026795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2753562602884254104071453 1032585976081595289026795)
                    ·
                      rfl

theorem cell22_3016431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 3].length) (baseStart_3016431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016431 prefixEnd_3016431 := by exact prefixLift 3016431
  have htrace : WordTrace (prefixWord ++ tailWord_3016431) baseStart_3016431 baseEnd_3016431 := by
    simpa [prefixWord, tailWord_3016431, baseEnd_3016431] using wordTrace_append hprefix tailTrace_3016431
  have hstable : (prefixWord ++ tailWord_3016431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016431).length < 2 ^ (prefixWord ++ tailWord_3016431).sum := by decide
  have hdescent : baseEnd_3016431 < baseStart_3016431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016472 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 7]
def baseStart_3016472 : Nat := 118140960795 + 3016472 * 2 ^ 59
def prefixEnd_3016472 : Nat := 4983230072969 + 3 ^ 40 * 3016472 * 2
def baseEnd_3016472 : Nat := 344200003739828282917223

theorem tailTrace_3016472 : CollatzResearch.WordTrace tailWord_3016472 prefixEnd_3016472 344200003739828282917223 := by
  unfold tailWord_3016472
  simp only [CollatzResearch.WordTrace]
  refine ⟨55009886163922295623869835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73346514885229727498493113 55009886163922295623869835)
  ·
    refine ⟨82514829245883443435804753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55009886163922295623869835 82514829245883443435804753)
    ·
      refine ⟨61886121934412582576853565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82514829245883443435804753 61886121934412582576853565)
      ·
        refine ⟨23207295725404718466320087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61886121934412582576853565 23207295725404718466320087)
        ·
          refine ⟨34810943588107077699480131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23207295725404718466320087 34810943588107077699480131)
          ·
            refine ⟨52216415382160616549220197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34810943588107077699480131 52216415382160616549220197)
            ·
              refine ⟨9790577884155115602978787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52216415382160616549220197 9790577884155115602978787)
              ·
                refine ⟨14685866826232673404468181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9790577884155115602978787 14685866826232673404468181)
                ·
                  refine ⟨344200003739828282917223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14685866826232673404468181 344200003739828282917223)
                  ·
                    rfl

theorem cell22_3016472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_3016472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016472 prefixEnd_3016472 := by exact prefixLift 3016472
  have htrace : WordTrace (prefixWord ++ tailWord_3016472) baseStart_3016472 baseEnd_3016472 := by
    simpa [prefixWord, tailWord_3016472, baseEnd_3016472] using wordTrace_append hprefix tailTrace_3016472
  have hstable : (prefixWord ++ tailWord_3016472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016472).length < 2 ^ (prefixWord ++ tailWord_3016472).sum := by decide
  have hdescent : baseEnd_3016472 < baseStart_3016472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016478 : List Nat := [4, 3, 2, 2, 1, 1, 2, 7]
def baseStart_3016478 : Nat := 118140960795 + 3016478 * 2 ^ 59
def prefixEnd_3016478 : Nat := 4983230072969 + 3 ^ 40 * 3016478 * 2
def baseEnd_3016478 : Nat := 114733562793566981455739

theorem tailTrace_3016478 : CollatzResearch.WordTrace tailWord_3016478 prefixEnd_3016478 114733562793566981455739 := by
  unfold tailWord_3016478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13752498895727856784057261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73346660777215236181638725 13752498895727856784057261)
  ·
    refine ⟨5157187085897946294021473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13752498895727856784057261 5157187085897946294021473)
    ·
      refine ⟨3867890314423459720516105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5157187085897946294021473 3867890314423459720516105)
      ·
        refine ⟨2900917735817594790387079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3867890314423459720516105 2900917735817594790387079)
        ·
          refine ⟨4351376603726392185580619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2900917735817594790387079 4351376603726392185580619)
          ·
            refine ⟨6527064905589588278370929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351376603726392185580619 6527064905589588278370929)
            ·
              refine ⟨4895298679192191208778197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6527064905589588278370929 4895298679192191208778197)
              ·
                refine ⟨114733562793566981455739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4895298679192191208778197 114733562793566981455739)
                ·
                  rfl

theorem cell22_3016478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_3016478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016478 prefixEnd_3016478 := by exact prefixLift 3016478
  have htrace : WordTrace (prefixWord ++ tailWord_3016478) baseStart_3016478 baseEnd_3016478 := by
    simpa [prefixWord, tailWord_3016478, baseEnd_3016478] using wordTrace_append hprefix tailTrace_3016478
  have hstable : (prefixWord ++ tailWord_3016478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016478).length < 2 ^ (prefixWord ++ tailWord_3016478).sum := by decide
  have hdescent : baseEnd_3016478 < baseStart_3016478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016519 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3016519 : Nat := 118140960795 + 3016519 * 2 ^ 59
def prefixEnd_3016519 : Nat := 4983230072969 + 3 ^ 40 * 3016519 * 2
def baseEnd_3016519 : Nat := 1032616100279992392826525

theorem tailTrace_3016519 : CollatzResearch.WordTrace tailWord_3016519 prefixEnd_3016519 1032616100279992392826525 := by
  unfold tailWord_3016519
  simp only [CollatzResearch.WordTrace]
  refine ⟨110021486558674318274700611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73347657705782878849800407 110021486558674318274700611)
  ·
    refine ⟨165032229838011477412050917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110021486558674318274700611 165032229838011477412050917)
    ·
      refine ⟨30943543094627152014759547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165032229838011477412050917 30943543094627152014759547)
      ·
        refine ⟨46415314641940728022139321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30943543094627152014759547 46415314641940728022139321)
        ·
          refine ⟨34811485981455546016604491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46415314641940728022139321 34811485981455546016604491)
          ·
            refine ⟨52217228972183319024906737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34811485981455546016604491 52217228972183319024906737)
            ·
              refine ⟨39162921729137489268680053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52217228972183319024906737 39162921729137489268680053)
              ·
                refine ⟨3671523912106639618938755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39162921729137489268680053 3671523912106639618938755)
                ·
                  refine ⟨5507285868159959428408133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671523912106639618938755 5507285868159959428408133)
                  ·
                    refine ⟨1032616100279992392826525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507285868159959428408133 1032616100279992392826525)
                    ·
                      rfl

theorem cell22_3016519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3016519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016519 prefixEnd_3016519 := by exact prefixLift 3016519
  have htrace : WordTrace (prefixWord ++ tailWord_3016519) baseStart_3016519 baseEnd_3016519 := by
    simpa [prefixWord, tailWord_3016519, baseEnd_3016519] using wordTrace_append hprefix tailTrace_3016519
  have hstable : (prefixWord ++ tailWord_3016519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016519).length < 2 ^ (prefixWord ++ tailWord_3016519).sum := by decide
  have hdescent : baseEnd_3016519 < baseStart_3016519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016549 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_3016549 : Nat := 118140960795 + 3016549 * 2 ^ 59
def prefixEnd_3016549 : Nat := 4983230072969 + 3 ^ 40 * 3016549 * 2
def baseEnd_3016549 : Nat := 1032626369893082314576433

theorem tailTrace_3016549 : CollatzResearch.WordTrace tailWord_3016549 prefixEnd_3016549 1032626369893082314576433 := by
  unfold tailWord_3016549
  simp only [CollatzResearch.WordTrace]
  refine ⟨110022580748565633398292701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73348387165710422265528467 110022580748565633398292701)
  ·
    refine ⟨41258467780712112524359763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110022580748565633398292701 41258467780712112524359763)
    ·
      refine ⟨61887701671068168786539645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41258467780712112524359763 61887701671068168786539645)
      ·
        refine ⟨23207888126650563294952367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61887701671068168786539645 23207888126650563294952367)
        ·
          refine ⟨34811832189975844942428551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23207888126650563294952367 34811832189975844942428551)
          ·
            refine ⟨52217748284963767413642827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34811832189975844942428551 52217748284963767413642827)
            ·
              refine ⟨78326622427445651120464241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52217748284963767413642827 78326622427445651120464241)
              ·
                refine ⟨58744966820584238340348181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78326622427445651120464241 58744966820584238340348181)
                ·
                  refine ⟨2753670319714886172203821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58744966820584238340348181 2753670319714886172203821)
                  ·
                    refine ⟨1032626369893082314576433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2753670319714886172203821 1032626369893082314576433)
                    ·
                      rfl

theorem cell22_3016549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_3016549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016549 prefixEnd_3016549 := by exact prefixLift 3016549
  have htrace : WordTrace (prefixWord ++ tailWord_3016549) baseStart_3016549 baseEnd_3016549 := by
    simpa [prefixWord, tailWord_3016549, baseEnd_3016549] using wordTrace_append hprefix tailTrace_3016549
  have hstable : (prefixWord ++ tailWord_3016549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016549).length < 2 ^ (prefixWord ++ tailWord_3016549).sum := by decide
  have hdescent : baseEnd_3016549 < baseStart_3016549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016600 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 1, 5]
def baseStart_3016600 : Nat := 118140960795 + 3016600 * 2 ^ 59
def prefixEnd_3016600 : Nat := 4983230072969 + 3 ^ 40 * 3016600 * 2
def baseEnd_3016600 : Nat := 1032643828235335181551277

theorem tailTrace_3016600 : CollatzResearch.WordTrace tailWord_3016600 prefixEnd_3016600 1032643828235335181551277 := by
  unfold tailWord_3016600
  simp only [CollatzResearch.WordTrace]
  refine ⟨55012220435690434554199627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73349627247587246072266169 55012220435690434554199627)
  ·
    refine ⟨82518330653535651831299441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55012220435690434554199627 82518330653535651831299441)
    ·
      refine ⟨61888747990151738873474581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82518330653535651831299441 61888747990151738873474581)
      ·
        refine ⟨2901035062038362759694121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61888747990151738873474581 2901035062038362759694121)
        ·
          refine ⟨2175776296528772069770591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2901035062038362759694121 2175776296528772069770591)
          ·
            refine ⟨3263664444793158104655887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175776296528772069770591 3263664444793158104655887)
            ·
              refine ⟨4895496667189737156983831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263664444793158104655887 4895496667189737156983831)
              ·
                refine ⟨7343245000784605735475747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895496667189737156983831 7343245000784605735475747)
                ·
                  refine ⟨11014867501176908603213621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343245000784605735475747 11014867501176908603213621)
                  ·
                    refine ⟨1032643828235335181551277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11014867501176908603213621 1032643828235335181551277)
                    ·
                      rfl

theorem cell22_3016600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_3016600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016600 prefixEnd_3016600 := by exact prefixLift 3016600
  have htrace : WordTrace (prefixWord ++ tailWord_3016600) baseStart_3016600 baseEnd_3016600 := by
    simpa [prefixWord, tailWord_3016600, baseEnd_3016600] using wordTrace_append hprefix tailTrace_3016600
  have hstable : (prefixWord ++ tailWord_3016600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016600).length < 2 ^ (prefixWord ++ tailWord_3016600).sum := by decide
  have hdescent : baseEnd_3016600 < baseStart_3016600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016658 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_3016658 : Nat := 118140960795 + 3016658 * 2 ^ 59
def prefixEnd_3016658 : Nat := 4983230072969 + 3 ^ 40 * 3016658 * 2
def baseEnd_3016658 : Nat := 344221227606880787867033

theorem tailTrace_3016658 : CollatzResearch.WordTrace tailWord_3016658 prefixEnd_3016658 344221227606880787867033 := by
  unfold tailWord_3016658
  simp only [CollatzResearch.WordTrace]
  refine ⟨27506639076292686253502657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73351037536780496676007085 27506639076292686253502657)
  ·
    refine ⟨20629979307219514690126993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27506639076292686253502657 20629979307219514690126993)
    ·
      refine ⟨15472484480414636017595245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20629979307219514690126993 15472484480414636017595245)
      ·
        refine ⟨5802181680155488506598217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15472484480414636017595245 5802181680155488506598217)
        ·
          refine ⟨4351636260116616379948663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5802181680155488506598217 4351636260116616379948663)
          ·
            refine ⟨6527454390174924569922995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351636260116616379948663 6527454390174924569922995)
            ·
              refine ⟨9791181585262386854884493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6527454390174924569922995 9791181585262386854884493)
              ·
                refine ⟨3671693094473395070581685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9791181585262386854884493 3671693094473395070581685)
                ·
                  refine ⟨344221227606880787867033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3671693094473395070581685 344221227606880787867033)
                  ·
                    rfl

theorem cell22_3016658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_3016658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016658 prefixEnd_3016658 := by exact prefixLift 3016658
  have htrace : WordTrace (prefixWord ++ tailWord_3016658) baseStart_3016658 baseEnd_3016658 := by
    simpa [prefixWord, tailWord_3016658, baseEnd_3016658] using wordTrace_append hprefix tailTrace_3016658
  have hstable : (prefixWord ++ tailWord_3016658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016658).length < 2 ^ (prefixWord ++ tailWord_3016658).sum := by decide
  have hdescent : baseEnd_3016658 < baseStart_3016658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016671 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 3, 4]
def baseStart_3016671 : Nat := 118140960795 + 3016671 * 2 ^ 59
def prefixEnd_3016671 : Nat := 4983230072969 + 3 ^ 40 * 3016671 * 2
def baseEnd_3016671 : Nat := 1032668132986314663026059

theorem tailTrace_3016671 : CollatzResearch.WordTrace tailWord_3016671 prefixEnd_3016671 1032668132986314663026059 := by
  unfold tailWord_3016671
  simp only [CollatzResearch.WordTrace]
  refine ⟨110027030454123648234233867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73351353636082432156155911 110027030454123648234233867)
  ·
    refine ⟨165040545681185472351350801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110027030454123648234233867 165040545681185472351350801)
    ·
      refine ⟨123780409260889104263513101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165040545681185472351350801 123780409260889104263513101)
      ·
        refine ⟨46417653472833414098817413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123780409260889104263513101 46417653472833414098817413)
        ·
          refine ⟨8703310026156265143528265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46417653472833414098817413 8703310026156265143528265)
          ·
            refine ⟨6527482519617198857646199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8703310026156265143528265 6527482519617198857646199)
            ·
              refine ⟨9791223779425798286469299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6527482519617198857646199 9791223779425798286469299)
              ·
                refine ⟨14686835669138697429703949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9791223779425798286469299 14686835669138697429703949)
                ·
                  refine ⟨5507563375927011536138981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14686835669138697429703949 5507563375927011536138981)
                  ·
                    refine ⟨1032668132986314663026059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507563375927011536138981 1032668132986314663026059)
                    ·
                      rfl

theorem cell22_3016671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_3016671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016671 prefixEnd_3016671 := by exact prefixLift 3016671
  have htrace : WordTrace (prefixWord ++ tailWord_3016671) baseStart_3016671 baseEnd_3016671 := by
    simpa [prefixWord, tailWord_3016671, baseEnd_3016671] using wordTrace_append hprefix tailTrace_3016671
  have hstable : (prefixWord ++ tailWord_3016671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016671).length < 2 ^ (prefixWord ++ tailWord_3016671).sum := by decide
  have hdescent : baseEnd_3016671 < baseStart_3016671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016701 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_3016701 : Nat := 118140960795 + 3016701 * 2 ^ 59
def prefixEnd_3016701 : Nat := 4983230072969 + 3 ^ 40 * 3016701 * 2
def baseEnd_3016701 : Nat := 1032678402599404584775967

theorem tailTrace_3016701 : CollatzResearch.WordTrace tailWord_3016701 prefixEnd_3016701 1032678402599404584775967 := by
  unfold tailWord_3016701
  simp only [CollatzResearch.WordTrace]
  refine ⟨110028124644014963357825957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73352083096009975571883971 110028124644014963357825957)
  ·
    refine ⟨20630273370752805629592367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110028124644014963357825957 20630273370752805629592367)
    ·
      refine ⟨30945410056129208444388551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20630273370752805629592367 30945410056129208444388551)
      ·
        refine ⟨46418115084193812666582827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30945410056129208444388551 46418115084193812666582827)
        ·
          refine ⟨69627172626290718999874241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46418115084193812666582827 69627172626290718999874241)
          ·
            refine ⟨52220379469718039249905681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69627172626290718999874241 52220379469718039249905681)
            ·
              refine ⟨39165284602288529437429261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52220379469718039249905681 39165284602288529437429261)
              ·
                refine ⟨14686981725858198539035973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39165284602288529437429261 14686981725858198539035973)
                ·
                  refine ⟨2753809073598412226069245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14686981725858198539035973 2753809073598412226069245)
                  ·
                    refine ⟨1032678402599404584775967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2753809073598412226069245 1032678402599404584775967)
                    ·
                      rfl

theorem cell22_3016701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_3016701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016701 prefixEnd_3016701 := by exact prefixLift 3016701
  have htrace : WordTrace (prefixWord ++ tailWord_3016701) baseStart_3016701 baseEnd_3016701 := by
    simpa [prefixWord, tailWord_3016701, baseEnd_3016701] using wordTrace_append hprefix tailTrace_3016701
  have hstable : (prefixWord ++ tailWord_3016701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016701).length < 2 ^ (prefixWord ++ tailWord_3016701).sum := by decide
  have hdescent : baseEnd_3016701 < baseStart_3016701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016718 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_3016718 : Nat := 118140960795 + 3016718 * 2 ^ 59
def prefixEnd_3016718 : Nat := 4983230072969 + 3 ^ 40 * 3016718 * 2
def baseEnd_3016718 : Nat := 1032684222046822207100915

theorem tailTrace_3016718 : CollatzResearch.WordTrace tailWord_3016718 prefixEnd_3016718 1032684222046822207100915 := by
  unfold tailWord_3016718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753593085619171907649351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73352496456635583507463205 13753593085619171907649351)
  ·
    refine ⟨20630389628428757861474027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13753593085619171907649351 20630389628428757861474027)
    ·
      refine ⟨30945584442643136792211041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20630389628428757861474027 30945584442643136792211041)
      ·
        refine ⟨23209188331982352594158281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30945584442643136792211041 23209188331982352594158281)
        ·
          refine ⟨17406891248986764445618711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23209188331982352594158281 17406891248986764445618711)
          ·
            refine ⟨26110336873480146668428067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17406891248986764445618711 26110336873480146668428067)
            ·
              refine ⟨39165505310220220002642101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26110336873480146668428067 39165505310220220002642101)
              ·
                refine ⟨3671766122833145625247697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39165505310220220002642101 3671766122833145625247697)
                ·
                  refine ⟨2753824592124859218935773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3671766122833145625247697 2753824592124859218935773)
                  ·
                    refine ⟨1032684222046822207100915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2753824592124859218935773 1032684222046822207100915)
                    ·
                      rfl

theorem cell22_3016718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_3016718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016718 prefixEnd_3016718 := by exact prefixLift 3016718
  have htrace : WordTrace (prefixWord ++ tailWord_3016718) baseStart_3016718 baseEnd_3016718 := by
    simpa [prefixWord, tailWord_3016718, baseEnd_3016718] using wordTrace_append hprefix tailTrace_3016718
  have hstable : (prefixWord ++ tailWord_3016718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016718).length < 2 ^ (prefixWord ++ tailWord_3016718).sum := by decide
  have hdescent : baseEnd_3016718 < baseStart_3016718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016733 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3016733 : Nat := 118140960795 + 3016733 * 2 ^ 59
def prefixEnd_3016733 : Nat := 4983230072969 + 3 ^ 40 * 3016733 * 2
def baseEnd_3016733 : Nat := 1032689356853367167975869

theorem tailTrace_3016733 : CollatzResearch.WordTrace tailWord_3016733 prefixEnd_3016733 1032689356853367167975869 := by
  unfold tailWord_3016733
  simp only [CollatzResearch.WordTrace]
  refine ⟨110029291779899032822990853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73352861186599355215327235 110029291779899032822990853)
  ·
    refine ⟨20630492208731068654310785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110029291779899032822990853 20630492208731068654310785)
    ·
      refine ⟨15472869156548301490733089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20630492208731068654310785 15472869156548301490733089)
      ·
        refine ⟨11604651867411226118049817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15472869156548301490733089 11604651867411226118049817)
        ·
          refine ⟨8703488900558419588537363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11604651867411226118049817 8703488900558419588537363)
          ·
            refine ⟨13055233350837629382806045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703488900558419588537363 13055233350837629382806045)
            ·
              refine ⟨4895712506564111018552267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13055233350837629382806045 4895712506564111018552267)
              ·
                refine ⟨7343568759846166527828401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895712506564111018552267 7343568759846166527828401)
                ·
                  refine ⟨5507676569884624895871301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7343568759846166527828401 5507676569884624895871301)
                  ·
                    refine ⟨1032689356853367167975869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507676569884624895871301 1032689356853367167975869)
                    ·
                      rfl

theorem cell22_3016733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3016733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016733 prefixEnd_3016733 := by exact prefixLift 3016733
  have htrace : WordTrace (prefixWord ++ tailWord_3016733) baseStart_3016733 baseEnd_3016733 := by
    simpa [prefixWord, tailWord_3016733, baseEnd_3016733] using wordTrace_append hprefix tailTrace_3016733
  have hstable : (prefixWord ++ tailWord_3016733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016733).length < 2 ^ (prefixWord ++ tailWord_3016733).sum := by decide
  have hdescent : baseEnd_3016733 < baseStart_3016733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016840 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_3016840 : Nat := 118140960795 + 3016840 * 2 ^ 59
def prefixEnd_3016840 : Nat := 4983230072969 + 3 ^ 40 * 3016840 * 2
def baseEnd_3016840 : Nat := 1032725985140054555550541

theorem tailTrace_3016840 : CollatzResearch.WordTrace tailWord_3016840 prefixEnd_3016840 1032725985140054555550541 := by
  unfold tailWord_3016840
  simp only [CollatzResearch.WordTrace]
  refine ⟨55016597195255695048567987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73355462927007593398090649 55016597195255695048567987)
  ·
    refine ⟨82524895792883542572851981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55016597195255695048567987 82524895792883542572851981)
    ·
      refine ⟨30946835922331328464819493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82524895792883542572851981 30946835922331328464819493)
      ·
        refine ⟨5802531735437124087153655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30946835922331328464819493 5802531735437124087153655)
        ·
          refine ⟨8703797603155686130730483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5802531735437124087153655 8703797603155686130730483)
          ·
            refine ⟨13055696404733529196095725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703797603155686130730483 13055696404733529196095725)
            ·
              refine ⟨4895886151775073448535897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13055696404733529196095725 4895886151775073448535897)
              ·
                refine ⟨3671914613831305086401923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895886151775073448535897 3671914613831305086401923)
                ·
                  refine ⟨5507871920746957629602885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671914613831305086401923 5507871920746957629602885)
                  ·
                    refine ⟨1032725985140054555550541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507871920746957629602885 1032725985140054555550541)
                    ·
                      rfl

theorem cell22_3016840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_3016840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016840 prefixEnd_3016840 := by exact prefixLift 3016840
  have htrace : WordTrace (prefixWord ++ tailWord_3016840) baseStart_3016840 baseEnd_3016840 := by
    simpa [prefixWord, tailWord_3016840, baseEnd_3016840] using wordTrace_append hprefix tailTrace_3016840
  have hstable : (prefixWord ++ tailWord_3016840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016840).length < 2 ^ (prefixWord ++ tailWord_3016840).sum := by decide
  have hdescent : baseEnd_3016840 < baseStart_3016840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016900 : List Nat := [2, 3, 3, 1, 2, 2, 3, 6]
def baseStart_3016900 : Nat := 118140960795 + 3016900 * 2 ^ 59
def prefixEnd_3016900 : Nat := 4983230072969 + 3 ^ 40 * 3016900 * 2
def baseEnd_3016900 : Nat := 114749613818470488783373

theorem tailTrace_3016900 : CollatzResearch.WordTrace tailWord_3016900 prefixEnd_3016900 114749613818470488783373 := by
  unfold tailWord_3016900
  simp only [CollatzResearch.WordTrace]
  refine ⟨55017691385147010172160077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73356921846862680229546769 55017691385147010172160077)
  ·
    refine ⟨20631634269430128814560029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55017691385147010172160077 20631634269430128814560029)
    ·
      refine ⟨7736862851036298305460011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20631634269430128814560029 7736862851036298305460011)
      ·
        refine ⟨11605294276554447458190017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7736862851036298305460011 11605294276554447458190017)
        ·
          refine ⟨8703970707415835593642513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11605294276554447458190017 8703970707415835593642513)
          ·
            refine ⟨6527978030561876695231885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8703970707415835593642513 6527978030561876695231885)
            ·
              refine ⟨2447991761460703760711957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6527978030561876695231885 2447991761460703760711957)
              ·
                refine ⟨114749613818470488783373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2447991761460703760711957 114749613818470488783373)
                ·
                  rfl

theorem cell22_3016900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 6].length) (baseStart_3016900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016900 prefixEnd_3016900 := by exact prefixLift 3016900
  have htrace : WordTrace (prefixWord ++ tailWord_3016900) baseStart_3016900 baseEnd_3016900 := by
    simpa [prefixWord, tailWord_3016900, baseEnd_3016900] using wordTrace_append hprefix tailTrace_3016900
  have hstable : (prefixWord ++ tailWord_3016900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016900).length < 2 ^ (prefixWord ++ tailWord_3016900).sum := by decide
  have hdescent : baseEnd_3016900 < baseStart_3016900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016911 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 7]
def baseStart_3016911 : Nat := 118140960795 + 3016911 * 2 ^ 59
def prefixEnd_3016911 : Nat := 4983230072969 + 3 ^ 40 * 3016911 * 2
def baseEnd_3016911 : Nat := 344250096630344679008441

theorem tailTrace_3016911 : CollatzResearch.WordTrace tailWord_3016911 prefixEnd_3016911 344250096630344679008441 := by
  unfold tailWord_3016911
  simp only [CollatzResearch.WordTrace]
  refine ⟨110035783973254169222970587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73357189315502779481980391 110035783973254169222970587)
  ·
    refine ⟨165053675959881253834455881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110035783973254169222970587 165053675959881253834455881)
    ·
      refine ⟨123790256969910940375841911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165053675959881253834455881 123790256969910940375841911)
      ·
        refine ⟨185685385454866410563762867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123790256969910940375841911 185685385454866410563762867)
        ·
          refine ⟨278528078182299615845644301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185685385454866410563762867 278528078182299615845644301)
          ·
            refine ⟨104448029318362355942116613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278528078182299615845644301 104448029318362355942116613)
            ·
              refine ⟨19584005497192941739146865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104448029318362355942116613 19584005497192941739146865)
              ·
                refine ⟨14688004122894706304360149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19584005497192941739146865 14688004122894706304360149)
                ·
                  refine ⟨344250096630344679008441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14688004122894706304360149 344250096630344679008441)
                  ·
                    rfl

theorem cell22_3016911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 7].length) (baseStart_3016911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016911 prefixEnd_3016911 := by exact prefixLift 3016911
  have htrace : WordTrace (prefixWord ++ tailWord_3016911) baseStart_3016911 baseEnd_3016911 := by
    simpa [prefixWord, tailWord_3016911, baseEnd_3016911] using wordTrace_append hprefix tailTrace_3016911
  have hstable : (prefixWord ++ tailWord_3016911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016911).length < 2 ^ (prefixWord ++ tailWord_3016911).sum := by decide
  have hdescent : baseEnd_3016911 < baseStart_3016911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016943 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 2, 5]
def baseStart_3016943 : Nat := 118140960795 + 3016943 * 2 ^ 59
def prefixEnd_3016943 : Nat := 4983230072969 + 3 ^ 40 * 3016943 * 2
def baseEnd_3016943 : Nat := 1032761244144996620225225

theorem tailTrace_3016943 : CollatzResearch.WordTrace tailWord_3016943 prefixEnd_3016943 1032761244144996620225225 := by
  unfold tailWord_3016943
  simp only [CollatzResearch.WordTrace]
  refine ⟨110036951109138238688135483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73357967406092159125423655 110036951109138238688135483)
  ·
    refine ⟨165055426663707358032203225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110036951109138238688135483 165055426663707358032203225)
    ·
      refine ⟨123791569997780518524152419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165055426663707358032203225 123791569997780518524152419)
      ·
        refine ⟨185687354996670777786228629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123791569997780518524152419 185687354996670777786228629)
        ·
          refine ⟨8704094765468942708729467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185687354996670777786228629 8704094765468942708729467)
          ·
            refine ⟨13056142148203414063094201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8704094765468942708729467 13056142148203414063094201)
            ·
              refine ⟨9792106611152560547320651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13056142148203414063094201 9792106611152560547320651)
              ·
                refine ⟨14688159916728840820980977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9792106611152560547320651 14688159916728840820980977)
                ·
                  refine ⟨11016119937546630615735733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14688159916728840820980977 11016119937546630615735733)
                  ·
                    refine ⟨1032761244144996620225225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11016119937546630615735733 1032761244144996620225225)
                    ·
                      rfl

theorem cell22_3016943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_3016943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3016943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3016943 prefixEnd_3016943 := by exact prefixLift 3016943
  have htrace : WordTrace (prefixWord ++ tailWord_3016943) baseStart_3016943 baseEnd_3016943 := by
    simpa [prefixWord, tailWord_3016943, baseEnd_3016943] using wordTrace_append hprefix tailTrace_3016943
  have hstable : (prefixWord ++ tailWord_3016943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016943).length < 2 ^ (prefixWord ++ tailWord_3016943).sum := by decide
  have hdescent : baseEnd_3016943 < baseStart_3016943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017009 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 1, 4]
def baseStart_3017009 : Nat := 118140960795 + 3017009 * 2 ^ 59
def prefixEnd_3017009 : Nat := 4983230072969 + 3 ^ 40 * 3017009 * 2
def baseEnd_3017009 : Nat := 1032783837293794448075023

theorem tailTrace_3017009 : CollatzResearch.WordTrace tailWord_3017009 prefixEnd_3017009 1032783837293794448075023 := by
  unfold tailWord_3017009
  simp only [CollatzResearch.WordTrace]
  refine ⟨110039358326899131960038081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73359572217932754640025387 110039358326899131960038081)
  ·
    refine ⟨82529518745174348970028561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110039358326899131960038081 82529518745174348970028561)
    ·
      refine ⟨61897139058880761727521421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82529518745174348970028561 61897139058880761727521421)
      ·
        refine ⟨23211427147080285647820533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61897139058880761727521421 23211427147080285647820533)
        ·
          refine ⟨2176071295038776779483175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23211427147080285647820533 2176071295038776779483175)
          ·
            refine ⟨3264106942558165169224763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176071295038776779483175 3264106942558165169224763)
            ·
              refine ⟨4896160413837247753837145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3264106942558165169224763 4896160413837247753837145)
              ·
                refine ⟨3672120310377935815377859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896160413837247753837145 3672120310377935815377859)
                ·
                  refine ⟨5508180465566903723066789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672120310377935815377859 5508180465566903723066789)
                  ·
                    refine ⟨1032783837293794448075023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5508180465566903723066789 1032783837293794448075023)
                    ·
                      rfl

theorem cell22_3017009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_3017009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017009 prefixEnd_3017009 := by exact prefixLift 3017009
  have htrace : WordTrace (prefixWord ++ tailWord_3017009) baseStart_3017009 baseEnd_3017009 := by
    simpa [prefixWord, tailWord_3017009, baseEnd_3017009] using wordTrace_append hprefix tailTrace_3017009
  have hstable : (prefixWord ++ tailWord_3017009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017009).length < 2 ^ (prefixWord ++ tailWord_3017009).sum := by decide
  have hdescent : baseEnd_3017009 < baseStart_3017009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017018 : List Nat := [3, 1, 1, 1, 4, 2, 2, 8]
def baseStart_3017018 : Nat := 118140960795 + 3017018 * 2 ^ 59
def prefixEnd_3017018 : Nat := 4983230072969 + 3 ^ 40 * 3017018 * 2
def baseEnd_3017018 : Nat := 114754102019746824955555

theorem tailTrace_3017018 : CollatzResearch.WordTrace tailWord_3017018 prefixEnd_3017018 114754102019746824955555 := by
  unfold tailWord_3017018
  simp only [CollatzResearch.WordTrace]
  refine ⟨27509921645966631624278927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73359791055911017664743805 27509921645966631624278927)
  ·
    refine ⟨41264882468949947436418391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27509921645966631624278927 41264882468949947436418391)
    ·
      refine ⟨61897323703424921154627587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41264882468949947436418391 61897323703424921154627587)
      ·
        refine ⟨92845985555137381731941381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61897323703424921154627587 92845985555137381731941381)
        ·
          refine ⟨17408622291588259074739009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92845985555137381731941381 17408622291588259074739009)
          ·
            refine ⟨13056466718691194306054257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17408622291588259074739009 13056466718691194306054257)
            ·
              refine ⟨9792350039018395729540693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13056466718691194306054257 9792350039018395729540693)
              ·
                refine ⟨114754102019746824955555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9792350039018395729540693 114754102019746824955555)
                ·
                  rfl

theorem cell22_3017018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_3017018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017018 prefixEnd_3017018 := by exact prefixLift 3017018
  have htrace : WordTrace (prefixWord ++ tailWord_3017018) baseStart_3017018 baseEnd_3017018 := by
    simpa [prefixWord, tailWord_3017018, baseEnd_3017018] using wordTrace_append hprefix tailTrace_3017018
  have hstable : (prefixWord ++ tailWord_3017018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017018).length < 2 ^ (prefixWord ++ tailWord_3017018).sum := by decide
  have hdescent : baseEnd_3017018 < baseStart_3017018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017020 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_3017020 : Nat := 118140960795 + 3017020 * 2 ^ 59
def prefixEnd_3017020 : Nat := 4983230072969 + 3 ^ 40 * 3017020 * 2
def baseEnd_3017020 : Nat := 1032787602818594086049989

theorem tailTrace_3017020 : CollatzResearch.WordTrace tailWord_3017020 prefixEnd_3017020 1032787602818594086049989 := by
  unfold tailWord_3017020
  simp only [CollatzResearch.WordTrace]
  refine ⟨55019879764929640419344257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73359839686572853892459009 55019879764929640419344257)
  ·
    refine ⟨41264909823697230314508193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55019879764929640419344257 41264909823697230314508193)
    ·
      refine ⟨30948682367772922735881145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41264909823697230314508193 30948682367772922735881145)
      ·
        refine ⟨23211511775829692051910859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30948682367772922735881145 23211511775829692051910859)
        ·
          refine ⟨34817267663744538077866289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23211511775829692051910859 34817267663744538077866289)
          ·
            refine ⟨26112950747808403558399717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34817267663744538077866289 26112950747808403558399717)
            ·
              refine ⟨4896178265214075667199947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26112950747808403558399717 4896178265214075667199947)
              ·
                refine ⟨7344267397821113500799921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896178265214075667199947 7344267397821113500799921)
                ·
                  refine ⟨5508200548365835125599941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7344267397821113500799921 5508200548365835125599941)
                  ·
                    refine ⟨1032787602818594086049989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5508200548365835125599941 1032787602818594086049989)
                    ·
                      rfl

theorem cell22_3017020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_3017020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017020 prefixEnd_3017020 := by exact prefixLift 3017020
  have htrace : WordTrace (prefixWord ++ tailWord_3017020) baseStart_3017020 baseEnd_3017020 := by
    simpa [prefixWord, tailWord_3017020, baseEnd_3017020] using wordTrace_append hprefix tailTrace_3017020
  have hstable : (prefixWord ++ tailWord_3017020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017020).length < 2 ^ (prefixWord ++ tailWord_3017020).sum := by decide
  have hdescent : baseEnd_3017020 < baseStart_3017020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017050 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_3017050 : Nat := 118140960795 + 3017050 * 2 ^ 59
def prefixEnd_3017050 : Nat := 4983230072969 + 3 ^ 40 * 3017050 * 2
def baseEnd_3017050 : Nat := 1032797872431684007799897

theorem tailTrace_3017050 : CollatzResearch.WordTrace tailWord_3017050 prefixEnd_3017050 1032797872431684007799897 := by
  unfold tailWord_3017050
  simp only [CollatzResearch.WordTrace]
  refine ⟨27510213429937648990570151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73360569146500397308187069 27510213429937648990570151)
  ·
    refine ⟨41265320144906473485855227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27510213429937648990570151 41265320144906473485855227)
    ·
      refine ⟨61897980217359710228782841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41265320144906473485855227 61897980217359710228782841)
      ·
        refine ⟨46423485163019782671587131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61897980217359710228782841 46423485163019782671587131)
        ·
          refine ⟨69635227744529674007380697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46423485163019782671587131 69635227744529674007380697)
          ·
            refine ⟨52226420808397255505535523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69635227744529674007380697 52226420808397255505535523)
            ·
              refine ⟨78339631212595883258303285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52226420808397255505535523 78339631212595883258303285)
              ·
                refine ⟨7344340426180864055465933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78339631212595883258303285 7344340426180864055465933)
                ·
                  refine ⟨2754127659817824020799725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7344340426180864055465933 2754127659817824020799725)
                  ·
                    refine ⟨1032797872431684007799897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754127659817824020799725 1032797872431684007799897)
                    ·
                      rfl

theorem cell22_3017050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_3017050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017050 prefixEnd_3017050 := by exact prefixLift 3017050
  have htrace : WordTrace (prefixWord ++ tailWord_3017050) baseStart_3017050 baseEnd_3017050 := by
    simpa [prefixWord, tailWord_3017050, baseEnd_3017050] using wordTrace_append hprefix tailTrace_3017050
  have hstable : (prefixWord ++ tailWord_3017050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017050).length < 2 ^ (prefixWord ++ tailWord_3017050).sum := by decide
  have hdescent : baseEnd_3017050 < baseStart_3017050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017097 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 5]
def baseStart_3017097 : Nat := 118140960795 + 3017097 * 2 ^ 59
def prefixEnd_3017097 : Nat := 4983230072969 + 3 ^ 40 * 3017097 * 2
def baseEnd_3017097 : Nat := 344271320497397183958251

theorem tailTrace_3017097 : CollatzResearch.WordTrace tailWord_3017097 prefixEnd_3017097 344271320497397183958251 := by
  unfold tailWord_3017097
  simp only [CollatzResearch.WordTrace]
  refine ⟨110042567950580322989241545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73361711967053548659494363 110042567950580322989241545)
  ·
    refine ⟨82531925962935242241931159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110042567950580322989241545 82531925962935242241931159)
    ·
      refine ⟨123797888944402863362896739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82531925962935242241931159 123797888944402863362896739)
      ·
        refine ⟨185696833416604295044345109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123797888944402863362896739 185696833416604295044345109)
        ·
          refine ⟨8704539066403326330203677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185696833416604295044345109 8704539066403326330203677)
          ·
            refine ⟨3264202149901247373826379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8704539066403326330203677 3264202149901247373826379)
            ·
              refine ⟨4896303224851871060739569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3264202149901247373826379 4896303224851871060739569)
              ·
                refine ⟨3672227418638903295554677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896303224851871060739569 3672227418638903295554677)
                ·
                  refine ⟨344271320497397183958251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3672227418638903295554677 344271320497397183958251)
                  ·
                    rfl

theorem cell22_3017097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_3017097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017097 prefixEnd_3017097 := by exact prefixLift 3017097
  have htrace : WordTrace (prefixWord ++ tailWord_3017097) baseStart_3017097 baseEnd_3017097 := by
    simpa [prefixWord, tailWord_3017097, baseEnd_3017097] using wordTrace_append hprefix tailTrace_3017097
  have hstable : (prefixWord ++ tailWord_3017097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017097).length < 2 ^ (prefixWord ++ tailWord_3017097).sum := by decide
  have hdescent : baseEnd_3017097 < baseStart_3017097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017127 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3017127 : Nat := 118140960795 + 3017127 * 2 ^ 59
def prefixEnd_3017127 : Nat := 4983230072969 + 3 ^ 40 * 3017127 * 2
def baseEnd_3017127 : Nat := 1032824231105281473624661

theorem tailTrace_3017127 : CollatzResearch.WordTrace tailWord_3017127 prefixEnd_3017127 1032824231105281473624661 := by
  unfold tailWord_3017127
  simp only [CollatzResearch.WordTrace]
  refine ⟨110043662140471638112833635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73362441426981092075222423 110043662140471638112833635)
  ·
    refine ⟨165065493210707457169250453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110043662140471638112833635 165065493210707457169250453)
    ·
      refine ⟨7737444994251912054808615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165065493210707457169250453 7737444994251912054808615)
      ·
        refine ⟨11606167491377868082212923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737444994251912054808615 11606167491377868082212923)
        ·
          refine ⟨17409251237066802123319385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11606167491377868082212923 17409251237066802123319385)
          ·
            refine ⟨13056938427800101592489539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17409251237066802123319385 13056938427800101592489539)
            ·
              refine ⟨19585407641700152388734309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13056938427800101592489539 19585407641700152388734309)
              ·
                refine ⟨3672263932818778572887683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19585407641700152388734309 3672263932818778572887683)
                ·
                  refine ⟨5508395899228167859331525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672263932818778572887683 5508395899228167859331525)
                  ·
                    refine ⟨1032824231105281473624661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5508395899228167859331525 1032824231105281473624661)
                    ·
                      rfl

theorem cell22_3017127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3017127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017127 prefixEnd_3017127 := by exact prefixLift 3017127
  have htrace : WordTrace (prefixWord ++ tailWord_3017127) baseStart_3017127 baseEnd_3017127 := by
    simpa [prefixWord, tailWord_3017127, baseEnd_3017127] using wordTrace_append hprefix tailTrace_3017127
  have hstable : (prefixWord ++ tailWord_3017127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017127).length < 2 ^ (prefixWord ++ tailWord_3017127).sum := by decide
  have hdescent : baseEnd_3017127 < baseStart_3017127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017159 : List Nat := [1, 1, 4, 1, 1, 5, 3, 2, 4]
def baseStart_3017159 : Nat := 118140960795 + 3017159 * 2 ^ 59
def prefixEnd_3017159 : Nat := 4983230072969 + 3 ^ 40 * 3017159 * 2
def baseEnd_3017159 : Nat := 344278395119748018941521

theorem tailTrace_3017159 : CollatzResearch.WordTrace tailWord_3017159 prefixEnd_3017159 344278395119748018941521 := by
  unfold tailWord_3017159
  simp only [CollatzResearch.WordTrace]
  refine ⟨110044829276355707577998531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73363219517570471718665687 110044829276355707577998531)
  ·
    refine ⟨165067243914533561366997797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110044829276355707577998531 165067243914533561366997797)
    ·
      refine ⟨30950108233975042756312087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165067243914533561366997797 30950108233975042756312087)
      ·
        refine ⟨46425162350962564134468131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30950108233975042756312087 46425162350962564134468131)
        ·
          refine ⟨69637743526443846201702197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46425162350962564134468131 69637743526443846201702197)
          ·
            refine ⟨6528538455604110581409581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69637743526443846201702197 6528538455604110581409581)
            ·
              refine ⟨2448201920851541468028593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6528538455604110581409581 2448201920851541468028593)
              ·
                refine ⟨1836151440638656101021445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448201920851541468028593 1836151440638656101021445)
                ·
                  refine ⟨344278395119748018941521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836151440638656101021445 344278395119748018941521)
                  ·
                    rfl

theorem cell22_3017159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 4].length) (baseStart_3017159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017159 prefixEnd_3017159 := by exact prefixLift 3017159
  have htrace : WordTrace (prefixWord ++ tailWord_3017159) baseStart_3017159 baseEnd_3017159 := by
    simpa [prefixWord, tailWord_3017159, baseEnd_3017159] using wordTrace_append hprefix tailTrace_3017159
  have hstable : (prefixWord ++ tailWord_3017159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017159).length < 2 ^ (prefixWord ++ tailWord_3017159).sum := by decide
  have hdescent : baseEnd_3017159 < baseStart_3017159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017189 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_3017189 : Nat := 118140960795 + 3017189 * 2 ^ 59
def prefixEnd_3017189 : Nat := 4983230072969 + 3 ^ 40 * 3017189 * 2
def baseEnd_3017189 : Nat := 1032845454972333978574471

theorem tailTrace_3017189 : CollatzResearch.WordTrace tailWord_3017189 prefixEnd_3017189 1032845454972333978574471 := by
  unfold tailWord_3017189
  simp only [CollatzResearch.WordTrace]
  refine ⟨110045923466247022701590621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73363948977498015134393747 110045923466247022701590621)
  ·
    refine ⟨41267221299842633513096483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110045923466247022701590621 41267221299842633513096483)
    ·
      refine ⟨61900831949763950269644725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41267221299842633513096483 61900831949763950269644725)
      ·
        refine ⟨5803202995290370337779193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61900831949763950269644725 5803202995290370337779193)
        ·
          refine ⟨4352402246467777753334395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5803202995290370337779193 4352402246467777753334395)
          ·
            refine ⟨6528603369701666630001593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352402246467777753334395 6528603369701666630001593)
            ·
              refine ⟨4896452527276249972501195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6528603369701666630001593 4896452527276249972501195)
              ·
                refine ⟨7344678790914374958751793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896452527276249972501195 7344678790914374958751793)
                ·
                  refine ⟨5508509093185781219063845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7344678790914374958751793 5508509093185781219063845)
                  ·
                    refine ⟨1032845454972333978574471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5508509093185781219063845 1032845454972333978574471)
                    ·
                      rfl

theorem cell22_3017189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_3017189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017189 prefixEnd_3017189 := by exact prefixLift 3017189
  have htrace : WordTrace (prefixWord ++ tailWord_3017189) baseStart_3017189 baseEnd_3017189 := by
    simpa [prefixWord, tailWord_3017189, baseEnd_3017189] using wordTrace_append hprefix tailTrace_3017189
  have hstable : (prefixWord ++ tailWord_3017189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017189).length < 2 ^ (prefixWord ++ tailWord_3017189).sum := by decide
  have hdescent : baseEnd_3017189 < baseStart_3017189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017219 : List Nat := [1, 1, 1, 3, 2, 1, 5, 4, 1, 3]
def baseStart_3017219 : Nat := 118140960795 + 3017219 * 2 ^ 59
def prefixEnd_3017219 : Nat := 4983230072969 + 3 ^ 40 * 3017219 * 2
def baseEnd_3017219 : Nat := 1032855724585423900324379

theorem tailTrace_3017219 : CollatzResearch.WordTrace tailWord_3017219 prefixEnd_3017219 1032855724585423900324379 := by
  unfold tailWord_3017219
  simp only [CollatzResearch.WordTrace]
  refine ⟨110047017656138337825182711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73364678437425558550121807 110047017656138337825182711)
  ·
    refine ⟨165070526484207506737774067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110047017656138337825182711 165070526484207506737774067)
    ·
      refine ⟨247605789726311260106661101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165070526484207506737774067 247605789726311260106661101)
      ·
        refine ⟨92852171147366722539997913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247605789726311260106661101 92852171147366722539997913)
        ·
          refine ⟨69639128360525041904998435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92852171147366722539997913 69639128360525041904998435)
          ·
            refine ⟨104458692540787562857497653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69639128360525041904998435 104458692540787562857497653)
            ·
              refine ⟨9793002425698834017890405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104458692540787562857497653 9793002425698834017890405)
              ·
                refine ⟨1836187954818531378354451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9793002425698834017890405 1836187954818531378354451)
                ·
                  refine ⟨2754281932227797067531677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836187954818531378354451 2754281932227797067531677)
                  ·
                    refine ⟨1032855724585423900324379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754281932227797067531677 1032855724585423900324379)
                    ·
                      rfl

theorem cell22_3017219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 3].length) (baseStart_3017219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017219 prefixEnd_3017219 := by exact prefixLift 3017219
  have htrace : WordTrace (prefixWord ++ tailWord_3017219) baseStart_3017219 baseEnd_3017219 := by
    simpa [prefixWord, tailWord_3017219, baseEnd_3017219] using wordTrace_append hprefix tailTrace_3017219
  have hstable : (prefixWord ++ tailWord_3017219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017219).length < 2 ^ (prefixWord ++ tailWord_3017219).sum := by decide
  have hdescent : baseEnd_3017219 < baseStart_3017219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017236 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3017236 : Nat := 118140960795 + 3017236 * 2 ^ 59
def prefixEnd_3017236 : Nat := 4983230072969 + 3 ^ 40 * 3017236 * 2
def baseEnd_3017236 : Nat := 1032861544032841522649327

theorem tailTrace_3017236 : CollatzResearch.WordTrace tailWord_3017236 prefixEnd_3017236 1032861544032841522649327 := by
  unfold tailWord_3017236
  simp only [CollatzResearch.WordTrace]
  refine ⟨55023818848538374864275781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73365091798051166485701041 55023818848538374864275781)
  ·
    refine ⟨10316966034100945287051709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55023818848538374864275781 10316966034100945287051709)
    ·
      refine ⟨3868862262787854482644391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10316966034100945287051709 3868862262787854482644391)
      ·
        refine ⟨5803293394181781723966587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868862262787854482644391 5803293394181781723966587)
        ·
          refine ⟨8704940091272672585949881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5803293394181781723966587 8704940091272672585949881)
          ·
            refine ⟨6528705068454504439462411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8704940091272672585949881 6528705068454504439462411)
            ·
              refine ⟨9793057602681756659193617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6528705068454504439462411 9793057602681756659193617)
              ·
                refine ⟨7344793202011317494395213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9793057602681756659193617 7344793202011317494395213)
                ·
                  refine ⟨2754297450754244060398205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7344793202011317494395213 2754297450754244060398205)
                  ·
                    refine ⟨1032861544032841522649327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754297450754244060398205 1032861544032841522649327)
                    ·
                      rfl

theorem cell22_3017236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3017236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017236 prefixEnd_3017236 := by exact prefixLift 3017236
  have htrace : WordTrace (prefixWord ++ tailWord_3017236) baseStart_3017236 baseEnd_3017236 := by
    simpa [prefixWord, tailWord_3017236, baseEnd_3017236] using wordTrace_append hprefix tailTrace_3017236
  have hstable : (prefixWord ++ tailWord_3017236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017236).length < 2 ^ (prefixWord ++ tailWord_3017236).sum := by decide
  have hdescent : baseEnd_3017236 < baseStart_3017236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017277 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 6]
def baseStart_3017277 : Nat := 118140960795 + 3017277 * 2 ^ 59
def prefixEnd_3017277 : Nat := 4983230072969 + 3 ^ 40 * 3017277 * 2
def baseEnd_3017277 : Nat := 344291859723577027458067

theorem tailTrace_3017277 : CollatzResearch.WordTrace tailWord_3017277 prefixEnd_3017277 344291859723577027458067 := by
  unfold tailWord_3017277
  simp only [CollatzResearch.WordTrace]
  refine ⟨110049133089928213730794085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73366088726618809153862723 110049133089928213730794085)
  ·
    refine ⟨20634212454361540074523891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110049133089928213730794085 20634212454361540074523891)
    ·
      refine ⟨30951318681542310111785837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20634212454361540074523891 30951318681542310111785837)
      ·
        refine ⟨11606744505578366291919689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30951318681542310111785837 11606744505578366291919689)
        ·
          refine ⟨8705058379183774718939767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11606744505578366291919689 8705058379183774718939767)
          ·
            refine ⟨13057587568775662078409651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8705058379183774718939767 13057587568775662078409651)
            ·
              refine ⟨19586381353163493117614477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13057587568775662078409651 19586381353163493117614477)
              ·
                refine ⟨7344893007436309919105429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19586381353163493117614477 7344893007436309919105429)
                ·
                  refine ⟨344291859723577027458067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7344893007436309919105429 344291859723577027458067)
                  ·
                    rfl

theorem cell22_3017277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_3017277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017277 prefixEnd_3017277 := by exact prefixLift 3017277
  have htrace : WordTrace (prefixWord ++ tailWord_3017277) baseStart_3017277 baseEnd_3017277 := by
    simpa [prefixWord, tailWord_3017277, baseEnd_3017277] using wordTrace_append hprefix tailTrace_3017277
  have hstable : (prefixWord ++ tailWord_3017277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017277).length < 2 ^ (prefixWord ++ tailWord_3017277).sum := by decide
  have hdescent : baseEnd_3017277 < baseStart_3017277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017399 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 2, 5]
def baseStart_3017399 : Nat := 118140960795 + 3017399 * 2 ^ 59
def prefixEnd_3017399 : Nat := 4983230072969 + 3 ^ 40 * 3017399 * 2
def baseEnd_3017399 : Nat := 1032917342263963430823827

theorem tailTrace_3017399 : CollatzResearch.WordTrace tailWord_3017399 prefixEnd_3017399 1032917342263963430823827 := by
  unfold tailWord_3017399
  simp only [CollatzResearch.WordTrace]
  refine ⟨110053582795486228566735251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73369055196990819044490167 110053582795486228566735251)
  ·
    refine ⟨165080374193229342850102877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110053582795486228566735251 165080374193229342850102877)
    ·
      refine ⟨61905140322461003568788579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165080374193229342850102877 61905140322461003568788579)
      ·
        refine ⟨92857710483691505353182869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61905140322461003568788579 92857710483691505353182869)
        ·
          refine ⟨4352705178923039313430447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92857710483691505353182869 4352705178923039313430447)
          ·
            refine ⟨6529057768384558970145671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352705178923039313430447 6529057768384558970145671)
            ·
              refine ⟨9793586652576838455218507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6529057768384558970145671 9793586652576838455218507)
              ·
                refine ⟨14690379978865257682827761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9793586652576838455218507 14690379978865257682827761)
                ·
                  refine ⟨11017784984148943262120821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14690379978865257682827761 11017784984148943262120821)
                  ·
                    refine ⟨1032917342263963430823827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11017784984148943262120821 1032917342263963430823827)
                    ·
                      rfl

theorem cell22_3017399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_3017399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017399 prefixEnd_3017399 := by exact prefixLift 3017399
  have htrace : WordTrace (prefixWord ++ tailWord_3017399) baseStart_3017399 baseEnd_3017399 := by
    simpa [prefixWord, tailWord_3017399, baseEnd_3017399] using wordTrace_append hprefix tailTrace_3017399
  have hstable : (prefixWord ++ tailWord_3017399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017399).length < 2 ^ (prefixWord ++ tailWord_3017399).sum := by decide
  have hdescent : baseEnd_3017399 < baseStart_3017399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017431 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 1, 4]
def baseStart_3017431 : Nat := 118140960795 + 3017431 * 2 ^ 59
def prefixEnd_3017431 : Nat := 4983230072969 + 3 ^ 40 * 3017431 * 2
def baseEnd_3017431 : Nat := 1032928296517926014023729

theorem tailTrace_3017431 : CollatzResearch.WordTrace tailWord_3017431 prefixEnd_3017431 1032928296517926014023729 := by
  unfold tailWord_3017431
  simp only [CollatzResearch.WordTrace]
  refine ⟨110054749931370298031900147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73369833287580198687933431 110054749931370298031900147)
  ·
    refine ⟨165082124897055447047850221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110054749931370298031900147 165082124897055447047850221)
    ·
      refine ⟨61905796836395792642943833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165082124897055447047850221 61905796836395792642943833)
      ·
        refine ⟨46429347627296844482207875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61905796836395792642943833 46429347627296844482207875)
        ·
          refine ⟨69644021440945266723311813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46429347627296844482207875 69644021440945266723311813)
          ·
            refine ⟨13058254020177237510620965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69644021440945266723311813 13058254020177237510620965)
            ·
              refine ⟨2448422628783232033241431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13058254020177237510620965 2448422628783232033241431)
              ·
                refine ⟨3672633943174848049862147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2448422628783232033241431 3672633943174848049862147)
                ·
                  refine ⟨5508950914762272074793221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672633943174848049862147 5508950914762272074793221)
                  ·
                    refine ⟨1032928296517926014023729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5508950914762272074793221 1032928296517926014023729)
                    ·
                      rfl

theorem cell22_3017431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_3017431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017431 prefixEnd_3017431 := by exact prefixLift 3017431
  have htrace : WordTrace (prefixWord ++ tailWord_3017431) baseStart_3017431 baseEnd_3017431 := by
    simpa [prefixWord, tailWord_3017431, baseEnd_3017431] using wordTrace_append hprefix tailTrace_3017431
  have hstable : (prefixWord ++ tailWord_3017431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017431).length < 2 ^ (prefixWord ++ tailWord_3017431).sum := by decide
  have hdescent : baseEnd_3017431 < baseStart_3017431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017457 : List Nat := [1, 2, 2, 2, 2, 2, 2, 9]
def baseStart_3017457 : Nat := 118140960795 + 3017457 * 2 ^ 59
def prefixEnd_3017457 : Nat := 4983230072969 + 3 ^ 40 * 3017457 * 2
def baseEnd_3017457 : Nat := 114770799649918956985961

theorem tailTrace_3017457 : CollatzResearch.WordTrace tailWord_3017457 prefixEnd_3017457 114770799649918956985961 := by
  unfold tailWord_3017457
  simp only [CollatzResearch.WordTrace]
  refine ⟨110055698229276104472346625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73370465486184069648231083 110055698229276104472346625)
  ·
    refine ⟨82541773671957078354259969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110055698229276104472346625 82541773671957078354259969)
    ·
      refine ⟨61906330253967808765694977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82541773671957078354259969 61906330253967808765694977)
      ·
        refine ⟨46429747690475856574271233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61906330253967808765694977 46429747690475856574271233)
        ·
          refine ⟨34822310767856892430703425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46429747690475856574271233 34822310767856892430703425)
          ·
            refine ⟨26116733075892669323027569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34822310767856892430703425 26116733075892669323027569)
            ·
              refine ⟨19587549806919501992270677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26116733075892669323027569 19587549806919501992270677)
              ·
                refine ⟨114770799649918956985961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19587549806919501992270677 114770799649918956985961)
                ·
                  rfl

theorem cell22_3017457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 9].length) (baseStart_3017457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017457 prefixEnd_3017457 := by exact prefixLift 3017457
  have htrace : WordTrace (prefixWord ++ tailWord_3017457) baseStart_3017457 baseEnd_3017457 := by
    simpa [prefixWord, tailWord_3017457, baseEnd_3017457] using wordTrace_append hprefix tailTrace_3017457
  have hstable : (prefixWord ++ tailWord_3017457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017457).length < 2 ^ (prefixWord ++ tailWord_3017457).sum := by decide
  have hdescent : baseEnd_3017457 < baseStart_3017457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017489 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 5, 3]
def baseStart_3017489 : Nat := 118140960795 + 3017489 * 2 ^ 59
def prefixEnd_3017489 : Nat := 4983230072969 + 3 ^ 40 * 3017489 * 2
def baseEnd_3017489 : Nat := 1032948151103233196073551

theorem tailTrace_3017489 : CollatzResearch.WordTrace tailWord_3017489 prefixEnd_3017489 1032948151103233196073551 := by
  unfold tailWord_3017489
  simp only [CollatzResearch.WordTrace]
  refine ⟨110056865365160173937511521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73371243576773449291674347 110056865365160173937511521)
  ·
    refine ⟨82542649023870130453133641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110056865365160173937511521 82542649023870130453133641)
    ·
      refine ⟨61906986767902597839850231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82542649023870130453133641 61906986767902597839850231)
      ·
        refine ⟨92860480151853896759775347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61906986767902597839850231 92860480151853896759775347)
        ·
          refine ⟨139290720227780845139663021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92860480151853896759775347 139290720227780845139663021)
          ·
            refine ⟨52234020085417816927373633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139290720227780845139663021 52234020085417816927373633)
            ·
              refine ⟨39175515064063362695530225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52234020085417816927373633 39175515064063362695530225)
              ·
                refine ⟨29381636298047522021647669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39175515064063362695530225 29381636298047522021647669)
                ·
                  refine ⟨2754528402941955189529469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29381636298047522021647669 2754528402941955189529469)
                  ·
                    refine ⟨1032948151103233196073551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754528402941955189529469 1032948151103233196073551)
                    ·
                      rfl

theorem cell22_3017489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_3017489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017489 prefixEnd_3017489 := by exact prefixLift 3017489
  have htrace : WordTrace (prefixWord ++ tailWord_3017489) baseStart_3017489 baseEnd_3017489 := by
    simpa [prefixWord, tailWord_3017489, baseEnd_3017489] using wordTrace_append hprefix tailTrace_3017489
  have hstable : (prefixWord ++ tailWord_3017489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017489).length < 2 ^ (prefixWord ++ tailWord_3017489).sum := by decide
  have hdescent : baseEnd_3017489 < baseStart_3017489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017579 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 1, 5]
def baseStart_3017579 : Nat := 118140960795 + 3017579 * 2 ^ 59
def prefixEnd_3017579 : Nat := 4983230072969 + 3 ^ 40 * 3017579 * 2
def baseEnd_3017579 : Nat := 1032978959942502961323275

theorem tailTrace_3017579 : CollatzResearch.WordTrace tailWord_3017579 prefixEnd_3017579 1032978959942502961323275 := by
  unfold tailWord_3017579
  simp only [CollatzResearch.WordTrace]
  refine ⟨110060147934834119308287791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73373431956556079538858527 110060147934834119308287791)
  ·
    refine ⟨165090221902251178962431687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110060147934834119308287791 165090221902251178962431687)
    ·
      refine ⟨247635332853376768443647531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165090221902251178962431687 247635332853376768443647531)
      ·
        refine ⟨371452999280065152665471297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247635332853376768443647531 371452999280065152665471297)
        ·
          refine ⟨278589749460048864499103473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371452999280065152665471297 278589749460048864499103473)
          ·
            refine ⟨208942312095036648374327605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278589749460048864499103473 208942312095036648374327605)
            ·
              refine ⟨19588341758909685785093213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208942312095036648374327605 19588341758909685785093213)
              ·
                refine ⟨7345628159591132169409955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19588341758909685785093213 7345628159591132169409955)
                ·
                  refine ⟨11018442239386698254114933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7345628159591132169409955 11018442239386698254114933)
                  ·
                    refine ⟨1032978959942502961323275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11018442239386698254114933 1032978959942502961323275)
                    ·
                      rfl

theorem cell22_3017579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_3017579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017579 prefixEnd_3017579 := by exact prefixLift 3017579
  have htrace : WordTrace (prefixWord ++ tailWord_3017579) baseStart_3017579 baseEnd_3017579 := by
    simpa [prefixWord, tailWord_3017579, baseEnd_3017579] using wordTrace_append hprefix tailTrace_3017579
  have hstable : (prefixWord ++ tailWord_3017579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017579).length < 2 ^ (prefixWord ++ tailWord_3017579).sum := by decide
  have hdescent : baseEnd_3017579 < baseStart_3017579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017609 : List Nat := [1, 2, 1, 1, 5, 3, 9]
def baseStart_3017609 : Nat := 118140960795 + 3017609 * 2 ^ 59
def prefixEnd_3017609 : Nat := 4983230072969 + 3 ^ 40 * 3017609 * 2
def baseEnd_3017609 : Nat := 38258860353910847521229

theorem tailTrace_3017609 : CollatzResearch.WordTrace tailWord_3017609 prefixEnd_3017609 38258860353910847521229 := by
  unfold tailWord_3017609
  simp only [CollatzResearch.WordTrace]
  refine ⟨110061242124725434431879881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73374161416483622954586587 110061242124725434431879881)
  ·
    refine ⟨82545931593544075823909911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110061242124725434431879881 82545931593544075823909911)
    ·
      refine ⟨123818897390316113735864867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82545931593544075823909911 123818897390316113735864867)
      ·
        refine ⟨185728346085474170603797301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123818897390316113735864867 185728346085474170603797301)
        ·
          refine ⟨17412032445513203494105997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185728346085474170603797301 17412032445513203494105997)
          ·
            refine ⟨6529512167067451310289749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17412032445513203494105997 6529512167067451310289749)
            ·
              refine ⟨38258860353910847521229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6529512167067451310289749 38258860353910847521229)
              ·
                rfl

theorem cell22_3017609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 9].length) (baseStart_3017609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017609 prefixEnd_3017609 := by exact prefixLift 3017609
  have htrace : WordTrace (prefixWord ++ tailWord_3017609) baseStart_3017609 baseEnd_3017609 := by
    simpa [prefixWord, tailWord_3017609, baseEnd_3017609] using wordTrace_append hprefix tailTrace_3017609
  have hstable : (prefixWord ++ tailWord_3017609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017609).length < 2 ^ (prefixWord ++ tailWord_3017609).sum := by decide
  have hdescent : baseEnd_3017609 < baseStart_3017609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017641 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 3, 3]
def baseStart_3017641 : Nat := 118140960795 + 3017641 * 2 ^ 59
def prefixEnd_3017641 : Nat := 4983230072969 + 3 ^ 40 * 3017641 * 2
def baseEnd_3017641 : Nat := 1033000183809555466273085

theorem tailTrace_3017641 : CollatzResearch.WordTrace tailWord_3017641 prefixEnd_3017641 1033000183809555466273085 := by
  unfold tailWord_3017641
  simp only [CollatzResearch.WordTrace]
  refine ⟨110062409260609503897044777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73374939507073002598029851 110062409260609503897044777)
  ·
    refine ⟨82546806945457127922783583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110062409260609503897044777 82546806945457127922783583)
    ·
      refine ⟨123820210418185691884175375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82546806945457127922783583 123820210418185691884175375)
      ·
        refine ⟨185730315627278537826263063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123820210418185691884175375 185730315627278537826263063)
        ·
          refine ⟨278595473440917806739394595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185730315627278537826263063 278595473440917806739394595)
          ·
            refine ⟨417893210161376710109091893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278595473440917806739394595 417893210161376710109091893)
            ·
              refine ⟨39177488452629066572727365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 417893210161376710109091893 39177488452629066572727365)
              ·
                refine ⟨7345779084867949982386381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39177488452629066572727365 7345779084867949982386381)
                ·
                  refine ⟨2754667156825481243394893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7345779084867949982386381 2754667156825481243394893)
                  ·
                    refine ⟨1033000183809555466273085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754667156825481243394893 1033000183809555466273085)
                    ·
                      rfl

theorem cell22_3017641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_3017641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017641 prefixEnd_3017641 := by exact prefixLift 3017641
  have htrace : WordTrace (prefixWord ++ tailWord_3017641) baseStart_3017641 baseEnd_3017641 := by
    simpa [prefixWord, tailWord_3017641, baseEnd_3017641] using wordTrace_append hprefix tailTrace_3017641
  have hstable : (prefixWord ++ tailWord_3017641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017641).length < 2 ^ (prefixWord ++ tailWord_3017641).sum := by decide
  have hdescent : baseEnd_3017641 < baseStart_3017641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017677 : List Nat := [1, 6, 3, 1, 1, 1, 2, 7]
def baseStart_3017677 : Nat := 118140960795 + 3017677 * 2 ^ 59
def prefixEnd_3017677 : Nat := 4983230072969 + 3 ^ 40 * 3017677 * 2
def baseEnd_3017677 : Nat := 114779167482807041374775

theorem tailTrace_3017677 : CollatzResearch.WordTrace tailWord_3017677 prefixEnd_3017677 114779167482807041374775 := by
  unfold tailWord_3017677
  simp only [CollatzResearch.WordTrace]
  refine ⟨110063722288479082045355285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73375814858986054696903523 110063722288479082045355285)
  ·
    refine ⟨5159236982272456970876029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110063722288479082045355285 5159236982272456970876029)
    ·
      refine ⟨1934713868352171364078511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5159236982272456970876029 1934713868352171364078511)
      ·
        refine ⟨2902070802528257046117767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934713868352171364078511 2902070802528257046117767)
        ·
          refine ⟨4353106203792385569176651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2902070802528257046117767 4353106203792385569176651)
          ·
            refine ⟨6529659305688578353764977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353106203792385569176651 6529659305688578353764977)
            ·
              refine ⟨4897244479266433765323733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6529659305688578353764977 4897244479266433765323733)
              ·
                refine ⟨114779167482807041374775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4897244479266433765323733 114779167482807041374775)
                ·
                  rfl

theorem cell22_3017677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 7].length) (baseStart_3017677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017677 prefixEnd_3017677 := by exact prefixLift 3017677
  have htrace : WordTrace (prefixWord ++ tailWord_3017677) baseStart_3017677 baseEnd_3017677 := by
    simpa [prefixWord, tailWord_3017677, baseEnd_3017677] using wordTrace_append hprefix tailTrace_3017677
  have hstable : (prefixWord ++ tailWord_3017677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017677).length < 2 ^ (prefixWord ++ tailWord_3017677).sum := by decide
  have hdescent : baseEnd_3017677 < baseStart_3017677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017688 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 5]
def baseStart_3017688 : Nat := 118140960795 + 3017688 * 2 ^ 59
def prefixEnd_3017688 : Nat := 4983230072969 + 3 ^ 40 * 3017688 * 2
def baseEnd_3017688 : Nat := 344338757623354336782647

theorem tailTrace_3017688 : CollatzResearch.WordTrace tailWord_3017688 prefixEnd_3017688 344338757623354336782647 := by
  unfold tailWord_3017688
  simp only [CollatzResearch.WordTrace]
  refine ⟨55032061745719615462002859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73376082327626153949337145 55032061745719615462002859)
  ·
    refine ⟨82548092618579423193004289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55032061745719615462002859 82548092618579423193004289)
    ·
      refine ⟨61911069463934567394753217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82548092618579423193004289 61911069463934567394753217)
      ·
        refine ⟨46433302097950925546064913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61911069463934567394753217 46433302097950925546064913)
        ·
          refine ⟨34824976573463194159548685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46433302097950925546064913 34824976573463194159548685)
          ·
            refine ⟨13059366215048697809830757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34824976573463194159548685 13059366215048697809830757)
            ·
              refine ⟨2448631165321630839343267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13059366215048697809830757 2448631165321630839343267)
              ·
                refine ⟨3672946747982446259014901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2448631165321630839343267 3672946747982446259014901)
                ·
                  refine ⟨344338757623354336782647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3672946747982446259014901 344338757623354336782647)
                  ·
                    rfl

theorem cell22_3017688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_3017688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017688 prefixEnd_3017688 := by exact prefixLift 3017688
  have htrace : WordTrace (prefixWord ++ tailWord_3017688) baseStart_3017688 baseEnd_3017688 := by
    simpa [prefixWord, tailWord_3017688, baseEnd_3017688] using wordTrace_append hprefix tailTrace_3017688
  have hstable : (prefixWord ++ tailWord_3017688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017688).length < 2 ^ (prefixWord ++ tailWord_3017688).sum := by decide
  have hdescent : baseEnd_3017688 < baseStart_3017688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017726 : List Nat := [4, 2, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3017726 : Nat := 118140960795 + 3017726 * 2 ^ 59
def prefixEnd_3017726 : Nat := 4983230072969 + 3 ^ 40 * 3017726 * 2
def baseEnd_3017726 : Nat := 1033029281046643577897825

theorem tailTrace_3017726 : CollatzResearch.WordTrace tailWord_3017726 prefixEnd_3017726 1033029281046643577897825 := by
  unfold tailWord_3017726
  simp only [CollatzResearch.WordTrace]
  refine ⟨13758188683162695426736129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73377006310201042275926021 13758188683162695426736129)
  ·
    refine ⟨10318641512372021570052097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13758188683162695426736129 10318641512372021570052097)
    ·
      refine ⟨7738981134279016177539073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10318641512372021570052097 7738981134279016177539073)
      ·
        refine ⟨5804235850709262133154305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7738981134279016177539073 5804235850709262133154305)
        ·
          refine ⟨4353176888031946599865729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5804235850709262133154305 4353176888031946599865729)
          ·
            refine ⟨3264882666023959949899297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4353176888031946599865729 3264882666023959949899297)
            ·
              refine ⟨2448661999517969962424473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264882666023959949899297 2448661999517969962424473)
              ·
                refine ⟨1836496499638477471818355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448661999517969962424473 1836496499638477471818355)
                ·
                  refine ⟨2754744749457716207727533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836496499638477471818355 2754744749457716207727533)
                  ·
                    refine ⟨1033029281046643577897825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754744749457716207727533 1033029281046643577897825)
                    ·
                      rfl

theorem cell22_3017726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3017726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017726 prefixEnd_3017726 := by exact prefixLift 3017726
  have htrace : WordTrace (prefixWord ++ tailWord_3017726) baseStart_3017726 baseEnd_3017726 := by
    simpa [prefixWord, tailWord_3017726, baseEnd_3017726] using wordTrace_append hprefix tailTrace_3017726
  have hstable : (prefixWord ++ tailWord_3017726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017726).length < 2 ^ (prefixWord ++ tailWord_3017726).sum := by decide
  have hdescent : baseEnd_3017726 < baseStart_3017726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017733 : List Nat := [1, 3, 1, 1, 2, 3, 3, 4, 4]
def baseStart_3017733 : Nat := 118140960795 + 3017733 * 2 ^ 59
def prefixEnd_3017733 : Nat := 4983230072969 + 3 ^ 40 * 3017733 * 2
def baseEnd_3017733 : Nat := 344343892429899297657601

theorem tailTrace_3017733 : CollatzResearch.WordTrace tailWord_3017733 prefixEnd_3017733 344343892429899297657601 := by
  unfold tailWord_3017733
  simp only [CollatzResearch.WordTrace]
  refine ⟨110065764776276203609393853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73377176517517469072929235 110065764776276203609393853)
  ·
    refine ⟨41274661791103576353522695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110065764776276203609393853 41274661791103576353522695)
    ·
      refine ⟨61911992686655364530284043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41274661791103576353522695 61911992686655364530284043)
      ·
        refine ⟨92867989029983046795426065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61911992686655364530284043 92867989029983046795426065)
        ·
          refine ⟨69650991772487285096569549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92867989029983046795426065 69650991772487285096569549)
          ·
            refine ⟨26119121914682731911213581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69650991772487285096569549 26119121914682731911213581)
            ·
              refine ⟨9794670718006024466705093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26119121914682731911213581 9794670718006024466705093)
              ·
                refine ⟨1836500759626129587507205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9794670718006024466705093 1836500759626129587507205)
                ·
                  refine ⟨344343892429899297657601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836500759626129587507205 344343892429899297657601)
                  ·
                    rfl

theorem cell22_3017733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_3017733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017733 prefixEnd_3017733 := by exact prefixLift 3017733
  have htrace : WordTrace (prefixWord ++ tailWord_3017733) baseStart_3017733 baseEnd_3017733 := by
    simpa [prefixWord, tailWord_3017733, baseEnd_3017733] using wordTrace_append hprefix tailTrace_3017733
  have hstable : (prefixWord ++ tailWord_3017733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017733).length < 2 ^ (prefixWord ++ tailWord_3017733).sum := by decide
  have hdescent : baseEnd_3017733 < baseStart_3017733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017763 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 2, 4]
def baseStart_3017763 : Nat := 118140960795 + 3017763 * 2 ^ 59
def prefixEnd_3017763 : Nat := 4983230072969 + 3 ^ 40 * 3017763 * 2
def baseEnd_3017763 : Nat := 1033041946902787814722711

theorem tailTrace_3017763 : CollatzResearch.WordTrace tailWord_3017763 prefixEnd_3017763 1033041946902787814722711 := by
  unfold tailWord_3017763
  simp only [CollatzResearch.WordTrace]
  refine ⟨110066858966167518732985943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73377905977445012488657295 110066858966167518732985943)
  ·
    refine ⟨165100288449251278099478915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110066858966167518732985943 165100288449251278099478915)
    ·
      refine ⟨247650432673876917149218373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165100288449251278099478915 247650432673876917149218373)
      ·
        refine ⟨46434456126351921965478445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247650432673876917149218373 46434456126351921965478445)
        ·
          refine ⟨17412921047381970737054417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46434456126351921965478445 17412921047381970737054417)
          ·
            refine ⟨13059690785536478052790813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17412921047381970737054417 13059690785536478052790813)
            ·
              refine ⟨4897384044576179269796555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13059690785536478052790813 4897384044576179269796555)
              ·
                refine ⟨7346076066864268904694833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897384044576179269796555 7346076066864268904694833)
                ·
                  refine ⟨5509557050148201678521125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7346076066864268904694833 5509557050148201678521125)
                  ·
                    refine ⟨1033041946902787814722711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5509557050148201678521125 1033041946902787814722711)
                    ·
                      rfl

theorem cell22_3017763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 4].length) (baseStart_3017763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017763 prefixEnd_3017763 := by exact prefixLift 3017763
  have htrace : WordTrace (prefixWord ++ tailWord_3017763) baseStart_3017763 baseEnd_3017763 := by
    simpa [prefixWord, tailWord_3017763, baseEnd_3017763] using wordTrace_append hprefix tailTrace_3017763
  have hstable : (prefixWord ++ tailWord_3017763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017763).length < 2 ^ (prefixWord ++ tailWord_3017763).sum := by decide
  have hdescent : baseEnd_3017763 < baseStart_3017763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017767 : List Nat := [1, 1, 7, 1, 1, 2, 2, 3, 4]
def baseStart_3017767 : Nat := 118140960795 + 3017767 * 2 ^ 59
def prefixEnd_3017767 : Nat := 4983230072969 + 3 ^ 40 * 3017767 * 2
def baseEnd_3017767 : Nat := 344347772061511045874233

theorem tailTrace_3017767 : CollatzResearch.WordTrace tailWord_3017767 prefixEnd_3017767 344347772061511045874233 := by
  unfold tailWord_3017767
  simp only [CollatzResearch.WordTrace]
  refine ⟨110067004858153027416131555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73378003238768684944087703 110067004858153027416131555)
  ·
    refine ⟨165100507287229541124197333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110067004858153027416131555 165100507287229541124197333)
    ·
      refine ⟨3869543139544442370098375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 165100507287229541124197333 3869543139544442370098375)
      ·
        refine ⟨5804314709316663555147563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3869543139544442370098375 5804314709316663555147563)
        ·
          refine ⟨8706472063974995332721345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5804314709316663555147563 8706472063974995332721345)
          ·
            refine ⟨6529854047981246499541009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8706472063974995332721345 6529854047981246499541009)
            ·
              refine ⟨4897390535985934874655757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6529854047981246499541009 4897390535985934874655757)
              ·
                refine ⟨1836521450994725577995909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4897390535985934874655757 1836521450994725577995909)
                ·
                  refine ⟨344347772061511045874233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836521450994725577995909 344347772061511045874233)
                  ·
                    rfl

theorem cell22_3017767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 4].length) (baseStart_3017767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017767 prefixEnd_3017767 := by exact prefixLift 3017767
  have htrace : WordTrace (prefixWord ++ tailWord_3017767) baseStart_3017767 baseEnd_3017767 := by
    simpa [prefixWord, tailWord_3017767, baseEnd_3017767] using wordTrace_append hprefix tailTrace_3017767
  have hstable : (prefixWord ++ tailWord_3017767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017767).length < 2 ^ (prefixWord ++ tailWord_3017767).sum := by decide
  have hdescent : baseEnd_3017767 < baseStart_3017767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017782 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3017782 : Nat := 118140960795 + 3017782 * 2 ^ 59
def prefixEnd_3017782 : Nat := 4983230072969 + 3 ^ 40 * 3017782 * 2
def baseEnd_3017782 : Nat := 1033048450991078098497653

theorem tailTrace_3017782 : CollatzResearch.WordTrace tailWord_3017782 prefixEnd_3017782 1033048450991078098497653 := by
  unfold tailWord_3017782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879221997068667811120475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73378367968732456651951733 6879221997068667811120475)
  ·
    refine ⟨10318832995603001716680713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6879221997068667811120475 10318832995603001716680713)
    ·
      refine ⟨7739124746702251287510535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10318832995603001716680713 7739124746702251287510535)
      ·
        refine ⟨11608687120053376931265803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7739124746702251287510535 11608687120053376931265803)
        ·
          refine ⟨17413030680080065396898705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11608687120053376931265803 17413030680080065396898705)
          ·
            refine ⟨13059773010060049047674029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17413030680080065396898705 13059773010060049047674029)
            ·
              refine ⟨4897414878772518392877761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13059773010060049047674029 4897414878772518392877761)
              ·
                refine ⟨3673061159079388794658321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4897414878772518392877761 3673061159079388794658321)
                ·
                  refine ⟨2754795869309541595993741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3673061159079388794658321 2754795869309541595993741)
                  ·
                    refine ⟨1033048450991078098497653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754795869309541595993741 1033048450991078098497653)
                    ·
                      rfl

theorem cell22_3017782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3017782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017782 prefixEnd_3017782 := by exact prefixLift 3017782
  have htrace : WordTrace (prefixWord ++ tailWord_3017782) baseStart_3017782 baseEnd_3017782 := by
    simpa [prefixWord, tailWord_3017782, baseEnd_3017782] using wordTrace_append hprefix tailTrace_3017782
  have hstable : (prefixWord ++ tailWord_3017782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017782).length < 2 ^ (prefixWord ++ tailWord_3017782).sum := by decide
  have hdescent : baseEnd_3017782 < baseStart_3017782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017810 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3017810 : Nat := 118140960795 + 3017810 * 2 ^ 59
def prefixEnd_3017810 : Nat := 4983230072969 + 3 ^ 40 * 3017810 * 2
def baseEnd_3017810 : Nat := 1033058035963295358797567

theorem tailTrace_3017810 : CollatzResearch.WordTrace tailWord_3017810 prefixEnd_3017810 1033058035963295358797567 := by
  unfold tailWord_3017810
  simp only [CollatzResearch.WordTrace]
  refine ⟨27517143299249311439986721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73379048797998163839964589 27517143299249311439986721)
  ·
    refine ⟨20637857474436983579990041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27517143299249311439986721 20637857474436983579990041)
    ·
      refine ⟨15478393105827737684992531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20637857474436983579990041 15478393105827737684992531)
      ·
        refine ⟨23217589658741606527488797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15478393105827737684992531 23217589658741606527488797)
        ·
          refine ⟨8706596122028102447808299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23217589658741606527488797 8706596122028102447808299)
          ·
            refine ⟨13059894183042153671712449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8706596122028102447808299 13059894183042153671712449)
            ·
              refine ⟨9794920637281615253784337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13059894183042153671712449 9794920637281615253784337)
              ·
                refine ⟨7346190477961211440338253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9794920637281615253784337 7346190477961211440338253)
                ·
                  refine ⟨2754821429235454290126845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7346190477961211440338253 2754821429235454290126845)
                  ·
                    refine ⟨1033058035963295358797567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754821429235454290126845 1033058035963295358797567)
                    ·
                      rfl

theorem cell22_3017810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3017810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017810 prefixEnd_3017810 := by exact prefixLift 3017810
  have htrace : WordTrace (prefixWord ++ tailWord_3017810) baseStart_3017810 baseEnd_3017810 := by
    simpa [prefixWord, tailWord_3017810, baseEnd_3017810] using wordTrace_append hprefix tailTrace_3017810
  have hstable : (prefixWord ++ tailWord_3017810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017810).length < 2 ^ (prefixWord ++ tailWord_3017810).sum := by decide
  have hdescent : baseEnd_3017810 < baseStart_3017810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017853 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_3017853 : Nat := 118140960795 + 3017853 * 2 ^ 59
def prefixEnd_3017853 : Nat := 4983230072969 + 3 ^ 40 * 3017853 * 2
def baseEnd_3017853 : Nat := 1033072755742057579972435

theorem tailTrace_3017853 : CollatzResearch.WordTrace tailWord_3017853 prefixEnd_3017853 1033072755742057579972435 := by
  unfold tailWord_3017853
  simp only [CollatzResearch.WordTrace]
  refine ⟨110070141535841464103762213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73380094357227642735841475 110070141535841464103762213)
  ·
    refine ⟨20638151537970274519455415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110070141535841464103762213 20638151537970274519455415)
    ·
      refine ⟨30957227306955411779183123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20638151537970274519455415 30957227306955411779183123)
      ·
        refine ⟨46435840960433117668774685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30957227306955411779183123 46435840960433117668774685)
        ·
          refine ⟨17413440360162419125790507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46435840960433117668774685 17413440360162419125790507)
          ·
            refine ⟨26120160540243628688685761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17413440360162419125790507 26120160540243628688685761)
            ·
              refine ⟨19590120405182721516514321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26120160540243628688685761 19590120405182721516514321)
              ·
                refine ⟨14692590303887041137385741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19590120405182721516514321 14692590303887041137385741)
                ·
                  refine ⟨5509721363957640426519653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14692590303887041137385741 5509721363957640426519653)
                  ·
                    refine ⟨1033072755742057579972435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5509721363957640426519653 1033072755742057579972435)
                    ·
                      rfl

theorem cell22_3017853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_3017853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017853 prefixEnd_3017853 := by exact prefixLift 3017853
  have htrace : WordTrace (prefixWord ++ tailWord_3017853) baseStart_3017853 baseEnd_3017853 := by
    simpa [prefixWord, tailWord_3017853, baseEnd_3017853] using wordTrace_append hprefix tailTrace_3017853
  have hstable : (prefixWord ++ tailWord_3017853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017853).length < 2 ^ (prefixWord ++ tailWord_3017853).sum := by decide
  have hdescent : baseEnd_3017853 < baseStart_3017853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017857 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 5]
def baseStart_3017857 : Nat := 118140960795 + 3017857 * 2 ^ 59
def prefixEnd_3017857 : Nat := 4983230072969 + 3 ^ 40 * 3017857 * 2
def baseEnd_3017857 : Nat := 344358041674600967624141

theorem tailTrace_3017857 : CollatzResearch.WordTrace tailWord_3017857 prefixEnd_3017857 344358041674600967624141 := by
  unfold tailWord_3017857
  simp only [CollatzResearch.WordTrace]
  refine ⟨110070287427826972786907825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73380191618551315191271883 110070287427826972786907825)
  ·
    refine ⟨82552715570870229590180869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110070287427826972786907825 82552715570870229590180869)
    ·
      refine ⟨15478634169538168048158913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82552715570870229590180869 15478634169538168048158913)
      ·
        refine ⟨11608975627153626036119185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15478634169538168048158913 11608975627153626036119185)
        ·
          refine ⟨8706731720365219527089389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11608975627153626036119185 8706731720365219527089389)
          ·
            refine ⟨3265024395136957322658521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8706731720365219527089389 3265024395136957322658521)
            ·
              refine ⟨2448768296352717991993891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265024395136957322658521 2448768296352717991993891)
              ·
                refine ⟨3673152444529076987990837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2448768296352717991993891 3673152444529076987990837)
                ·
                  refine ⟨344358041674600967624141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3673152444529076987990837 344358041674600967624141)
                  ·
                    rfl

theorem cell22_3017857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_3017857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017857 prefixEnd_3017857 := by exact prefixLift 3017857
  have htrace : WordTrace (prefixWord ++ tailWord_3017857) baseStart_3017857 baseEnd_3017857 := by
    simpa [prefixWord, tailWord_3017857, baseEnd_3017857] using wordTrace_append hprefix tailTrace_3017857
  have hstable : (prefixWord ++ tailWord_3017857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017857).length < 2 ^ (prefixWord ++ tailWord_3017857).sum := by decide
  have hdescent : baseEnd_3017857 < baseStart_3017857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017870 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3017870 : Nat := 118140960795 + 3017870 * 2 ^ 59
def prefixEnd_3017870 : Nat := 4983230072969 + 3 ^ 40 * 3017870 * 2
def baseEnd_3017870 : Nat := 1033078575189475202297383

theorem tailTrace_3017870 : CollatzResearch.WordTrace tailWord_3017870 prefixEnd_3017870 1033078575189475202297383 := by
  unfold tailWord_3017870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13758845197097484500891383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73380507717853250671420709 13758845197097484500891383)
  ·
    refine ⟨20638267795646226751337075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13758845197097484500891383 20638267795646226751337075)
    ·
      refine ⟨30957401693469340127005613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20638267795646226751337075 30957401693469340127005613)
      ·
        refine ⟨11609025635051002547627105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30957401693469340127005613 11609025635051002547627105)
        ·
          refine ⟨8706769226288251910720329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11609025635051002547627105 8706769226288251910720329)
          ·
            refine ⟨6530076919716188933040247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8706769226288251910720329 6530076919716188933040247)
            ·
              refine ⟨9795115379574283399560371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530076919716188933040247 9795115379574283399560371)
              ·
                refine ⟨14692673069361425099340557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9795115379574283399560371 14692673069361425099340557)
                ·
                  refine ⟨5509752401010534412252709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14692673069361425099340557 5509752401010534412252709)
                  ·
                    refine ⟨1033078575189475202297383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5509752401010534412252709 1033078575189475202297383)
                    ·
                      rfl

theorem cell22_3017870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3017870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017870 prefixEnd_3017870 := by exact prefixLift 3017870
  have htrace : WordTrace (prefixWord ++ tailWord_3017870) baseStart_3017870 baseEnd_3017870 := by
    simpa [prefixWord, tailWord_3017870, baseEnd_3017870] using wordTrace_append hprefix tailTrace_3017870
  have hstable : (prefixWord ++ tailWord_3017870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017870).length < 2 ^ (prefixWord ++ tailWord_3017870).sum := by decide
  have hdescent : baseEnd_3017870 < baseStart_3017870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017885 : List Nat := [1, 4, 2, 1, 1, 2, 2, 5, 4]
def baseStart_3017885 : Nat := 118140960795 + 3017885 * 2 ^ 59
def prefixEnd_3017885 : Nat := 4983230072969 + 3 ^ 40 * 3017885 * 2
def baseEnd_3017885 : Nat := 344361236665340054390779

theorem tailTrace_3017885 : CollatzResearch.WordTrace tailWord_3017885 prefixEnd_3017885 344361236665340054390779 := by
  unfold tailWord_3017885
  simp only [CollatzResearch.WordTrace]
  refine ⟨110071308671725533568927109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73380872447817022379284739 110071308671725533568927109)
  ·
    refine ⟨20638370375948537544173833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110071308671725533568927109 20638370375948537544173833)
    ·
      refine ⟨15478777781961403158130375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20638370375948537544173833 15478777781961403158130375)
      ·
        refine ⟨23218166672942104737195563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15478777781961403158130375 23218166672942104737195563)
        ·
          refine ⟨34827250009413157105793345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23218166672942104737195563 34827250009413157105793345)
          ·
            refine ⟨26120437507059867829345009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34827250009413157105793345 26120437507059867829345009)
            ·
              refine ⟨19590328130294900872008757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26120437507059867829345009 19590328130294900872008757)
              ·
                refine ⟨1836593262215146956750821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19590328130294900872008757 1836593262215146956750821)
                ·
                  refine ⟨344361236665340054390779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836593262215146956750821 344361236665340054390779)
                  ·
                    rfl

theorem cell22_3017885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_3017885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017885 prefixEnd_3017885 := by exact prefixLift 3017885
  have htrace : WordTrace (prefixWord ++ tailWord_3017885) baseStart_3017885 baseEnd_3017885 := by
    simpa [prefixWord, tailWord_3017885, baseEnd_3017885] using wordTrace_append hprefix tailTrace_3017885
  have hstable : (prefixWord ++ tailWord_3017885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017885).length < 2 ^ (prefixWord ++ tailWord_3017885).sum := by decide
  have hdescent : baseEnd_3017885 < baseStart_3017885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017896 : List Nat := [2, 1, 19]
def baseStart_3017896 : Nat := 118140960795 + 3017896 * 2 ^ 59
def prefixEnd_3017896 : Nat := 4983230072969 + 3 ^ 40 * 3017896 * 2
def baseEnd_3017896 : Nat := 472376532016835757269

theorem tailTrace_3017896 : CollatzResearch.WordTrace tailWord_3017896 prefixEnd_3017896 472376532016835757269 := by
  unfold tailWord_3017896
  simp only [CollatzResearch.WordTrace]
  refine ⟨55035854937342841223788771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73381139916457121631718361 55035854937342841223788771)
  ·
    refine ⟨82553782406014261835683157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55035854937342841223788771 82553782406014261835683157)
    ·
      refine ⟨472376532016835757269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 19 82553782406014261835683157 472376532016835757269)
      ·
        rfl

theorem cell22_3017896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 19].length) (baseStart_3017896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017896 prefixEnd_3017896 := by exact prefixLift 3017896
  have htrace : WordTrace (prefixWord ++ tailWord_3017896) baseStart_3017896 baseEnd_3017896 := by
    simpa [prefixWord, tailWord_3017896, baseEnd_3017896] using wordTrace_append hprefix tailTrace_3017896
  have hstable : (prefixWord ++ tailWord_3017896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017896).length < 2 ^ (prefixWord ++ tailWord_3017896).sum := by decide
  have hdescent : baseEnd_3017896 < baseStart_3017896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017913 : List Nat := [1, 2, 1, 4, 1, 3, 3, 7]
def baseStart_3017913 : Nat := 118140960795 + 3017913 * 2 ^ 59
def prefixEnd_3017913 : Nat := 4983230072969 + 3 ^ 40 * 3017913 * 2
def baseEnd_3017913 : Nat := 114788143885359713719139

theorem tailTrace_3017913 : CollatzResearch.WordTrace tailWord_3017913 prefixEnd_3017913 114788143885359713719139 := by
  unfold tailWord_3017913
  simp only [CollatzResearch.WordTrace]
  refine ⟨110072329915624094350946393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73381553277082729567297595 110072329915624094350946393)
  ·
    refine ⟨82554247436718070763209795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110072329915624094350946393 82554247436718070763209795)
    ·
      refine ⟨123831371155077106144814693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82554247436718070763209795 123831371155077106144814693)
      ·
        refine ⟨23218382091576957402152755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123831371155077106144814693 23218382091576957402152755)
        ·
          refine ⟨34827573137365436103229133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23218382091576957402152755 34827573137365436103229133)
          ·
            refine ⟨13060339926512038538710925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34827573137365436103229133 13060339926512038538710925)
            ·
              refine ⟨4897627472442014452016597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13060339926512038538710925 4897627472442014452016597)
              ·
                refine ⟨114788143885359713719139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4897627472442014452016597 114788143885359713719139)
                ·
                  rfl

theorem cell22_3017913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 7].length) (baseStart_3017913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017913 prefixEnd_3017913 := by exact prefixLift 3017913
  have htrace : WordTrace (prefixWord ++ tailWord_3017913) baseStart_3017913 baseEnd_3017913 := by
    simpa [prefixWord, tailWord_3017913, baseEnd_3017913] using wordTrace_append hprefix tailTrace_3017913
  have hstable : (prefixWord ++ tailWord_3017913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017913).length < 2 ^ (prefixWord ++ tailWord_3017913).sum := by decide
  have hdescent : baseEnd_3017913 < baseStart_3017913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017930 : List Nat := [3, 1, 2, 1, 3, 3, 3, 6]
def baseStart_3017930 : Nat := 118140960795 + 3017930 * 2 ^ 59
def prefixEnd_3017930 : Nat := 4983230072969 + 3 ^ 40 * 3017930 * 2
def baseEnd_3017930 : Nat := 114788790490628338421911

theorem tailTrace_3017930 : CollatzResearch.WordTrace tailWord_3017930 prefixEnd_3017930 114788790490628338421911 := by
  unfold tailWord_3017930
  simp only [CollatzResearch.WordTrace]
  refine ⟨27518237489140626563578811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73381966637708337502876829 27518237489140626563578811)
  ·
    refine ⟨41277356233710939845368217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27518237489140626563578811 41277356233710939845368217)
    ·
      refine ⟨30958017175283204884026163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41277356233710939845368217 30958017175283204884026163)
      ·
        refine ⟨46437025762924807326039245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30958017175283204884026163 46437025762924807326039245)
        ·
          refine ⟨17413884661096802747264717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46437025762924807326039245 17413884661096802747264717)
          ·
            refine ⟨6530206747911301030224269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17413884661096802747264717 6530206747911301030224269)
            ·
              refine ⟨2448827530466737886334101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6530206747911301030224269 2448827530466737886334101)
              ·
                refine ⟨114788790490628338421911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2448827530466737886334101 114788790490628338421911)
                ·
                  rfl

theorem cell22_3017930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_3017930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017930 prefixEnd_3017930 := by exact prefixLift 3017930
  have htrace : WordTrace (prefixWord ++ tailWord_3017930) baseStart_3017930 baseEnd_3017930 := by
    simpa [prefixWord, tailWord_3017930, baseEnd_3017930] using wordTrace_append hprefix tailTrace_3017930
  have hstable : (prefixWord ++ tailWord_3017930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017930).length < 2 ^ (prefixWord ++ tailWord_3017930).sum := by decide
  have hdescent : baseEnd_3017930 < baseStart_3017930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017962 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_3017962 : Nat := 118140960795 + 3017962 * 2 ^ 59
def prefixEnd_3017962 : Nat := 4983230072969 + 3 ^ 40 * 3017962 * 2
def baseEnd_3017962 : Nat := 1033110068669617628997101

theorem tailTrace_3017962 : CollatzResearch.WordTrace tailWord_3017962 prefixEnd_3017962 1033110068669617628997101 := by
  unfold tailWord_3017962
  simp only [CollatzResearch.WordTrace]
  refine ⟨27518529273111643929870035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73382744728297717146320093 27518529273111643929870035)
  ·
    refine ⟨41277793909667465894805053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27518529273111643929870035 41277793909667465894805053)
    ·
      refine ⟨15479172716125299710551895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41277793909667465894805053 15479172716125299710551895)
      ·
        refine ⟨23218759074187949565827843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15479172716125299710551895 23218759074187949565827843)
        ·
          refine ⟨34828138611281924348741765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23218759074187949565827843 34828138611281924348741765)
          ·
            refine ⟨6530275989615360815389081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34828138611281924348741765 6530275989615360815389081)
            ·
              refine ⟨4897706992211520611541811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6530275989615360815389081 4897706992211520611541811)
              ·
                refine ⟨7346560488317280917312717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897706992211520611541811 7346560488317280917312717)
                ·
                  refine ⟨2754960183118980343992269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7346560488317280917312717 2754960183118980343992269)
                  ·
                    refine ⟨1033110068669617628997101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754960183118980343992269 1033110068669617628997101)
                    ·
                      rfl

theorem cell22_3017962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_3017962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3017962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3017962 prefixEnd_3017962 := by exact prefixLift 3017962
  have htrace : WordTrace (prefixWord ++ tailWord_3017962) baseStart_3017962 baseEnd_3017962 := by
    simpa [prefixWord, tailWord_3017962, baseEnd_3017962] using wordTrace_append hprefix tailTrace_3017962
  have hstable : (prefixWord ++ tailWord_3017962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017962).length < 2 ^ (prefixWord ++ tailWord_3017962).sum := by decide
  have hdescent : baseEnd_3017962 < baseStart_3017962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018048 : List Nat := [2, 1, 1, 2, 2, 1, 3, 10]
def baseStart_3018048 : Nat := 118140960795 + 3018048 * 2 ^ 59
def prefixEnd_3018048 : Nat := 4983230072969 + 3 ^ 40 * 3018048 * 2
def baseEnd_3018048 : Nat := 114793278691904674594093

theorem tailTrace_3018048 : CollatzResearch.WordTrace tailWord_3018048 prefixEnd_3018048 114793278691904674594093 := by
  unfold tailWord_3018048
  simp only [CollatzResearch.WordTrace]
  refine ⟨55038626885067506203555399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73384835846756674938073865 55038626885067506203555399)
  ·
    refine ⟨82557940327601259305333099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55038626885067506203555399 82557940327601259305333099)
    ·
      refine ⟨123836910491401888957999649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82557940327601259305333099 123836910491401888957999649)
      ·
        refine ⟨92877682868551416718499737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123836910491401888957999649 92877682868551416718499737)
        ·
          refine ⟨69658262151413562538874803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92877682868551416718499737 69658262151413562538874803)
          ·
            refine ⟨104487393227120343808312205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69658262151413562538874803 104487393227120343808312205)
            ·
              refine ⟨39182772460170128928117077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104487393227120343808312205 39182772460170128928117077)
              ·
                refine ⟨114793278691904674594093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39182772460170128928117077 114793278691904674594093)
                ·
                  rfl

theorem cell22_3018048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 10].length) (baseStart_3018048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018048 prefixEnd_3018048 := by exact prefixLift 3018048
  have htrace : WordTrace (prefixWord ++ tailWord_3018048) baseStart_3018048 baseEnd_3018048 := by
    simpa [prefixWord, tailWord_3018048, baseEnd_3018048] using wordTrace_append hprefix tailTrace_3018048
  have hstable : (prefixWord ++ tailWord_3018048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018048).length < 2 ^ (prefixWord ++ tailWord_3018048).sum := by decide
  have hdescent : baseEnd_3018048 < baseStart_3018048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018052 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3018052 : Nat := 118140960795 + 3018052 * 2 ^ 59
def prefixEnd_3018052 : Nat := 4983230072969 + 3 ^ 40 * 3018052 * 2
def baseEnd_3018052 : Nat := 1033140877508887394246825

theorem tailTrace_3018052 : CollatzResearch.WordTrace tailWord_3018052 prefixEnd_3018052 1033140877508887394246825 := by
  unfold tailWord_3018052
  simp only [CollatzResearch.WordTrace]
  refine ⟨55038699831060260545128205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73384933108080347393504273 55038699831060260545128205)
  ·
    refine ⟨20639512436647597704423077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55038699831060260545128205 20639512436647597704423077)
    ·
      refine ⟨3869908581871424569579327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20639512436647597704423077 3869908581871424569579327)
      ·
        refine ⟨5804862872807136854368991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3869908581871424569579327 5804862872807136854368991)
        ·
          refine ⟨8707294309210705281553487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5804862872807136854368991 8707294309210705281553487)
          ·
            refine ⟨13060941463816057922330231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707294309210705281553487 13060941463816057922330231)
            ·
              refine ⟨19591412195724086883495347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13060941463816057922330231 19591412195724086883495347)
              ·
                refine ⟨29387118293586130325243021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19591412195724086883495347 29387118293586130325243021)
                ·
                  refine ⟨11020169360094798871966133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29387118293586130325243021 11020169360094798871966133)
                  ·
                    refine ⟨1033140877508887394246825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11020169360094798871966133 1033140877508887394246825)
                    ·
                      rfl

theorem cell22_3018052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3018052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018052 prefixEnd_3018052 := by exact prefixLift 3018052
  have htrace : WordTrace (prefixWord ++ tailWord_3018052) baseStart_3018052 baseEnd_3018052 := by
    simpa [prefixWord, tailWord_3018052, baseEnd_3018052] using wordTrace_append hprefix tailTrace_3018052
  have hstable : (prefixWord ++ tailWord_3018052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018052).length < 2 ^ (prefixWord ++ tailWord_3018052).sum := by decide
  have hdescent : baseEnd_3018052 < baseStart_3018052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018063 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 4, 7]
def baseStart_3018063 : Nat := 118140960795 + 3018063 * 2 ^ 59
def prefixEnd_3018063 : Nat := 4983230072969 + 3 ^ 40 * 3018063 * 2
def baseEnd_3018063 : Nat := 1033144643033687032221791

theorem tailTrace_3018063 : CollatzResearch.WordTrace tailWord_3018063 prefixEnd_3018063 1033144643033687032221791 := by
  unfold tailWord_3018063
  simp only [CollatzResearch.WordTrace]
  refine ⟨110077800865080669968906843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73385200576720446645937895 110077800865080669968906843)
  ·
    refine ⟨165116701297621004953360265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110077800865080669968906843 165116701297621004953360265)
    ·
      refine ⟨123837525973215753715020199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165116701297621004953360265 123837525973215753715020199)
      ·
        refine ⟨185756288959823630572530299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123837525973215753715020199 185756288959823630572530299)
        ·
          refine ⟨278634433439735445858795449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185756288959823630572530299 278634433439735445858795449)
          ·
            refine ⟨208975825079801584394096587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278634433439735445858795449 208975825079801584394096587)
            ·
              refine ⟨313463737619702376591144881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208975825079801584394096587 313463737619702376591144881)
              ·
                refine ⟨235097803214776782443358661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313463737619702376591144881 235097803214776782443358661)
                ·
                  refine ⟨44080838102770646708129749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235097803214776782443358661 44080838102770646708129749)
                  ·
                    refine ⟨1033144643033687032221791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44080838102770646708129749 1033144643033687032221791)
                    ·
                      rfl

theorem cell22_3018063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_3018063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018063 prefixEnd_3018063 := by exact prefixLift 3018063
  have htrace : WordTrace (prefixWord ++ tailWord_3018063) baseStart_3018063 baseEnd_3018063 := by
    simpa [prefixWord, tailWord_3018063, baseEnd_3018063] using wordTrace_append hprefix tailTrace_3018063
  have hstable : (prefixWord ++ tailWord_3018063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018063).length < 2 ^ (prefixWord ++ tailWord_3018063).sum := by decide
  have hdescent : baseEnd_3018063 < baseStart_3018063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018069 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_3018069 : Nat := 118140960795 + 3018069 * 2 ^ 59
def prefixEnd_3018069 : Nat := 4983230072969 + 3 ^ 40 * 3018069 * 2
def baseEnd_3018069 : Nat := 1033146696956305016571773

theorem tailTrace_3018069 : CollatzResearch.WordTrace tailWord_3018069 prefixEnd_3018069 1033146696956305016571773 := by
  unfold tailWord_3018069
  simp only [CollatzResearch.WordTrace]
  refine ⟨110078019703058932993625261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73385346468705955329083507 110078019703058932993625261)
  ·
    refine ⟨41279257388647099872609473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110078019703058932993625261 41279257388647099872609473)
    ·
      refine ⟨30959443041485324904457105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41279257388647099872609473 30959443041485324904457105)
      ·
        refine ⟨23219582281113993678342829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30959443041485324904457105 23219582281113993678342829)
        ·
          refine ⟨8707343355417747629378561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23219582281113993678342829 8707343355417747629378561)
          ·
            refine ⟨6530507516563310722033921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8707343355417747629378561 6530507516563310722033921)
            ·
              refine ⟨4897880637422483041525441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6530507516563310722033921 4897880637422483041525441)
              ·
                refine ⟨3673410478066862281144081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4897880637422483041525441 3673410478066862281144081)
                ·
                  refine ⟨2755057858550146710858061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3673410478066862281144081 2755057858550146710858061)
                  ·
                    refine ⟨1033146696956305016571773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2755057858550146710858061 1033146696956305016571773)
                    ·
                      rfl

theorem cell22_3018069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_3018069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018069 prefixEnd_3018069 := by exact prefixLift 3018069
  have htrace : WordTrace (prefixWord ++ tailWord_3018069) baseStart_3018069 baseEnd_3018069 := by
    simpa [prefixWord, tailWord_3018069, baseEnd_3018069] using wordTrace_append hprefix tailTrace_3018069
  have hstable : (prefixWord ++ tailWord_3018069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018069).length < 2 ^ (prefixWord ++ tailWord_3018069).sum := by decide
  have hdescent : baseEnd_3018069 < baseStart_3018069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018101 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_3018101 : Nat := 118140960795 + 3018101 * 2 ^ 59
def prefixEnd_3018101 : Nat := 4983230072969 + 3 ^ 40 * 3018101 * 2
def baseEnd_3018101 : Nat := 1033157651210267599771675

theorem tailTrace_3018101 : CollatzResearch.WordTrace tailWord_3018101 prefixEnd_3018101 1033157651210267599771675 := by
  unfold tailWord_3018101
  simp only [CollatzResearch.WordTrace]
  refine ⟨110079186838943002458790157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73386124559295334972526771 110079186838943002458790157)
  ·
    refine ⟨41279695064603625922046309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110079186838943002458790157 41279695064603625922046309)
    ·
      refine ⟨7739942824613179860383683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41279695064603625922046309 7739942824613179860383683)
      ·
        refine ⟨11609914236919769790575525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7739942824613179860383683 11609914236919769790575525)
        ·
          refine ⟨2176858919422456835732911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11609914236919769790575525 2176858919422456835732911)
          ·
            refine ⟨3265288379133685253599367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176858919422456835732911 3265288379133685253599367)
            ·
              refine ⟨4897932568700527880399051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265288379133685253599367 4897932568700527880399051)
              ·
                refine ⟨7346898853050791820598577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897932568700527880399051 7346898853050791820598577)
                ·
                  refine ⟨5510174139788093865448933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7346898853050791820598577 5510174139788093865448933)
                  ·
                    refine ⟨1033157651210267599771675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5510174139788093865448933 1033157651210267599771675)
                    ·
                      rfl

theorem cell22_3018101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_3018101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018101 prefixEnd_3018101 := by exact prefixLift 3018101
  have htrace : WordTrace (prefixWord ++ tailWord_3018101) baseStart_3018101 baseEnd_3018101 := by
    simpa [prefixWord, tailWord_3018101, baseEnd_3018101] using wordTrace_append hprefix tailTrace_3018101
  have hstable : (prefixWord ++ tailWord_3018101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018101).length < 2 ^ (prefixWord ++ tailWord_3018101).sum := by decide
  have hdescent : baseEnd_3018101 < baseStart_3018101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018187 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 4, 3]
def baseStart_3018187 : Nat := 118140960795 + 3018187 * 2 ^ 59
def prefixEnd_3018187 : Nat := 4983230072969 + 3 ^ 40 * 3018187 * 2
def baseEnd_3018187 : Nat := 1033187090767792042121411

theorem tailTrace_3018187 : CollatzResearch.WordTrace tailWord_3018187 prefixEnd_3018187 1033187090767792042121411 := by
  unfold tailWord_3018187
  simp only [CollatzResearch.WordTrace]
  refine ⟨110082323516631439146420815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73388215677754292764280543 110082323516631439146420815)
  ·
    refine ⟨165123485274947158719631223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110082323516631439146420815 165123485274947158719631223)
    ·
      refine ⟨247685227912420738079446835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165123485274947158719631223 247685227912420738079446835)
      ·
        refine ⟨371527841868631107119170253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247685227912420738079446835 371527841868631107119170253)
        ·
          refine ⟨139322940700736665169688845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371527841868631107119170253 139322940700736665169688845)
          ·
            refine ⟨52246102762776249438633317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139322940700736665169688845 52246102762776249438633317)
            ·
              refine ⟨9796144268020546769743747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52246102762776249438633317 9796144268020546769743747)
              ·
                refine ⟨14694216402030820154615621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796144268020546769743747 14694216402030820154615621)
                ·
                  refine ⟨2755165575380778778990429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14694216402030820154615621 2755165575380778778990429)
                  ·
                    refine ⟨1033187090767792042121411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2755165575380778778990429 1033187090767792042121411)
                    ·
                      rfl

theorem cell22_3018187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 3].length) (baseStart_3018187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018187 prefixEnd_3018187 := by exact prefixLift 3018187
  have htrace : WordTrace (prefixWord ++ tailWord_3018187) baseStart_3018187 baseEnd_3018187 := by
    simpa [prefixWord, tailWord_3018187, baseEnd_3018187] using wordTrace_append hprefix tailTrace_3018187
  have hstable : (prefixWord ++ tailWord_3018187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018187).length < 2 ^ (prefixWord ++ tailWord_3018187).sum := by decide
  have hdescent : baseEnd_3018187 < baseStart_3018187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018200 : List Nat := [2, 1, 2, 2, 2, 1, 3, 9]
def baseStart_3018200 : Nat := 118140960795 + 3018200 * 2 ^ 59
def prefixEnd_3018200 : Nat := 4983230072969 + 3 ^ 40 * 3018200 * 2
def baseEnd_3018200 : Nat := 114799060103718260171819

theorem tailTrace_3018200 : CollatzResearch.WordTrace tailWord_3018200 prefixEnd_3018200 114799060103718260171819 := by
  unfold tailWord_3018200
  simp only [CollatzResearch.WordTrace]
  refine ⟨55041398832792171183322027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73388531777056228244429369 55041398832792171183322027)
  ·
    refine ⟨82562098249188256774983041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55041398832792171183322027 82562098249188256774983041)
    ·
      refine ⟨61921573686891192581237281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82562098249188256774983041 61921573686891192581237281)
      ·
        refine ⟨46441180265168394435927961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61921573686891192581237281 46441180265168394435927961)
        ·
          refine ⟨34830885198876295826945971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46441180265168394435927961 34830885198876295826945971)
          ·
            refine ⟨52246327798314443740418957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34830885198876295826945971 52246327798314443740418957)
            ·
              refine ⟨19592372924367916402657109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52246327798314443740418957 19592372924367916402657109)
              ·
                refine ⟨114799060103718260171819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19592372924367916402657109 114799060103718260171819)
                ·
                  rfl

theorem cell22_3018200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 9].length) (baseStart_3018200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018200 prefixEnd_3018200 := by exact prefixLift 3018200
  have htrace : WordTrace (prefixWord ++ tailWord_3018200) baseStart_3018200 baseEnd_3018200 := by
    simpa [prefixWord, tailWord_3018200, baseEnd_3018200] using wordTrace_append hprefix tailTrace_3018200
  have hstable : (prefixWord ++ tailWord_3018200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018200).length < 2 ^ (prefixWord ++ tailWord_3018200).sum := by decide
  have hdescent : baseEnd_3018200 < baseStart_3018200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018247 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3018247 : Nat := 118140960795 + 3018247 * 2 ^ 59
def prefixEnd_3018247 : Nat := 4983230072969 + 3 ^ 40 * 3018247 * 2
def baseEnd_3018247 : Nat := 1033207629993971885621227

theorem tailTrace_3018247 : CollatzResearch.WordTrace tailWord_3018247 prefixEnd_3018247 1033207629993971885621227 := by
  unfold tailWord_3018247
  simp only [CollatzResearch.WordTrace]
  refine ⟨110084511896414069393604995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73389674597609379595736663 110084511896414069393604995)
  ·
    refine ⟨165126767844621104090407493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110084511896414069393604995 165126767844621104090407493)
    ·
      refine ⟨30961268970866457016951405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165126767844621104090407493 30961268970866457016951405)
      ·
        refine ⟨11610475864074921381356777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30961268970866457016951405 11610475864074921381356777)
        ·
          refine ⟨8707856898056191036017583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11610475864074921381356777 8707856898056191036017583)
          ·
            refine ⟨13061785347084286554026375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707856898056191036017583 13061785347084286554026375)
            ·
              refine ⟨19592678020626429831039563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13061785347084286554026375 19592678020626429831039563)
              ·
                refine ⟨29389017030939644746559345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19592678020626429831039563 29389017030939644746559345)
                ·
                  refine ⟨22041762773204733559919509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29389017030939644746559345 22041762773204733559919509)
                  ·
                    refine ⟨1033207629993971885621227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22041762773204733559919509 1033207629993971885621227)
                    ·
                      rfl

theorem cell22_3018247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3018247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018247 prefixEnd_3018247 := by exact prefixLift 3018247
  have htrace : WordTrace (prefixWord ++ tailWord_3018247) baseStart_3018247 baseEnd_3018247 := by
    simpa [prefixWord, tailWord_3018247, baseEnd_3018247] using wordTrace_append hprefix tailTrace_3018247
  have hstable : (prefixWord ++ tailWord_3018247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018247).length < 2 ^ (prefixWord ++ tailWord_3018247).sum := by decide
  have hdescent : baseEnd_3018247 < baseStart_3018247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018337 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3018337 : Nat := 118140960795 + 3018337 * 2 ^ 59
def prefixEnd_3018337 : Nat := 4983230072969 + 3 ^ 40 * 3018337 * 2
def baseEnd_3018337 : Nat := 1033238438833241650870951

theorem tailTrace_3018337 : CollatzResearch.WordTrace tailWord_3018337 prefixEnd_3018337 1033238438833241650870951 := by
  unfold tailWord_3018337
  simp only [CollatzResearch.WordTrace]
  refine ⟨110087794466088014764381265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73391862977392009842920843 110087794466088014764381265)
  ·
    refine ⟨82565845849566011073285949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110087794466088014764381265 82565845849566011073285949)
    ·
      refine ⟨30962192193587254152482231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82565845849566011073285949 30962192193587254152482231)
      ·
        refine ⟨46443288290380881228723347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30962192193587254152482231 46443288290380881228723347)
        ·
          refine ⟨69664932435571321843085021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46443288290380881228723347 69664932435571321843085021)
          ·
            refine ⟨26124349663339245691156883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69664932435571321843085021 26124349663339245691156883)
            ·
              refine ⟨39186524495008868536735325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26124349663339245691156883 39186524495008868536735325)
              ·
                refine ⟨14694946685628325701275747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39186524495008868536735325 14694946685628325701275747)
                ·
                  refine ⟨22042420028442488551913621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14694946685628325701275747 22042420028442488551913621)
                  ·
                    refine ⟨1033238438833241650870951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22042420028442488551913621 1033238438833241650870951)
                    ·
                      rfl

theorem cell22_3018337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3018337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018337 prefixEnd_3018337 := by exact prefixLift 3018337
  have htrace : WordTrace (prefixWord ++ tailWord_3018337) baseStart_3018337 baseEnd_3018337 := by
    simpa [prefixWord, tailWord_3018337, baseEnd_3018337] using wordTrace_append hprefix tailTrace_3018337
  have hstable : (prefixWord ++ tailWord_3018337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018337).length < 2 ^ (prefixWord ++ tailWord_3018337).sum := by decide
  have hdescent : baseEnd_3018337 < baseStart_3018337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018339 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 4, 3]
def baseStart_3018339 : Nat := 118140960795 + 3018339 * 2 ^ 59
def prefixEnd_3018339 : Nat := 4983230072969 + 3 ^ 40 * 3018339 * 2
def baseEnd_3018339 : Nat := 1033239123474114312320945

theorem tailTrace_3018339 : CollatzResearch.WordTrace tailWord_3018339 prefixEnd_3018339 1033239123474114312320945 := by
  unfold tailWord_3018339
  simp only [CollatzResearch.WordTrace]
  refine ⟨110087867412080769105954071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73391911608053846070636047 110087867412080769105954071)
  ·
    refine ⟨165131801118121153658931107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110087867412080769105954071 165131801118121153658931107)
    ·
      refine ⟨247697701677181730488396661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165131801118121153658931107 247697701677181730488396661)
      ·
        refine ⟨23221659532235787233287187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247697701677181730488396661 23221659532235787233287187)
        ·
          refine ⟨34832489298353680849930781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23221659532235787233287187 34832489298353680849930781)
          ·
            refine ⟨13062183486882630318724043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34832489298353680849930781 13062183486882630318724043)
            ·
              refine ⟨19593275230323945478086065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062183486882630318724043 19593275230323945478086065)
              ·
                refine ⟨14694956422742959108564549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19593275230323945478086065 14694956422742959108564549)
                ·
                  refine ⟨2755304329264304832855853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14694956422742959108564549 2755304329264304832855853)
                  ·
                    refine ⟨1033239123474114312320945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2755304329264304832855853 1033239123474114312320945)
                    ·
                      rfl

theorem cell22_3018339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 3].length) (baseStart_3018339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018339 prefixEnd_3018339 := by exact prefixLift 3018339
  have htrace : WordTrace (prefixWord ++ tailWord_3018339) baseStart_3018339 baseEnd_3018339 := by
    simpa [prefixWord, tailWord_3018339, baseEnd_3018339] using wordTrace_append hprefix tailTrace_3018339
  have hstable : (prefixWord ++ tailWord_3018339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018339).length < 2 ^ (prefixWord ++ tailWord_3018339).sum := by decide
  have hdescent : baseEnd_3018339 < baseStart_3018339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018341 : List Nat := [1, 3, 1, 3, 3, 1, 3, 3, 4]
def baseStart_3018341 : Nat := 118140960795 + 3018341 * 2 ^ 59
def prefixEnd_3018341 : Nat := 4983230072969 + 3 ^ 40 * 3018341 * 2
def baseEnd_3018341 : Nat := 344413269371662324590313

theorem tailTrace_3018341 : CollatzResearch.WordTrace tailWord_3018341 prefixEnd_3018341 344413269371662324590313 := by
  unfold tailWord_3018341
  simp only [CollatzResearch.WordTrace]
  refine ⟨110087940358073523447526877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73391960238715682298351251 110087940358073523447526877)
  ·
    refine ⟨41282977634277571292822579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110087940358073523447526877 41282977634277571292822579)
    ·
      refine ⟨61924466451416356939233869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41282977634277571292822579 61924466451416356939233869)
      ·
        refine ⟨23221674919281133852212701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61924466451416356939233869 23221674919281133852212701)
        ·
          refine ⟨8708128094730425194579763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23221674919281133852212701 8708128094730425194579763)
          ·
            refine ⟨13062192142095637791869645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708128094730425194579763 13062192142095637791869645)
            ·
              refine ⟨4898322053285864171951117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13062192142095637791869645 4898322053285864171951117)
              ·
                refine ⟨1836870769982199064481669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4898322053285864171951117 1836870769982199064481669)
                ·
                  refine ⟨344413269371662324590313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836870769982199064481669 344413269371662324590313)
                  ·
                    rfl

theorem cell22_3018341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_3018341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018341 prefixEnd_3018341 := by exact prefixLift 3018341
  have htrace : WordTrace (prefixWord ++ tailWord_3018341) baseStart_3018341 baseEnd_3018341 := by
    simpa [prefixWord, tailWord_3018341, baseEnd_3018341] using wordTrace_append hprefix tailTrace_3018341
  have hstable : (prefixWord ++ tailWord_3018341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018341).length < 2 ^ (prefixWord ++ tailWord_3018341).sum := by decide
  have hdescent : baseEnd_3018341 < baseStart_3018341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018352 : List Nat := [2, 1, 1, 1, 6, 1, 10]
def baseStart_3018352 : Nat := 118140960795 + 3018352 * 2 ^ 59
def prefixEnd_3018352 : Nat := 4983230072969 + 3 ^ 40 * 3018352 * 2
def baseEnd_3018352 : Nat := 38268280505177281916515

theorem tailTrace_3018352 : CollatzResearch.WordTrace tailWord_3018352 prefixEnd_3018352 38268280505177281916515 := by
  unfold tailWord_3018352
  simp only [CollatzResearch.WordTrace]
  refine ⟨55044170780516836163088655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73392227707355781550784873 55044170780516836163088655)
  ·
    refine ⟨82566256170775254244632983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55044170780516836163088655 82566256170775254244632983)
    ·
      refine ⟨123849384256162881366949475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82566256170775254244632983 123849384256162881366949475)
      ·
        refine ⟨185774076384244322050424213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123849384256162881366949475 185774076384244322050424213)
        ·
          refine ⟨8708159830511452596113635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185774076384244322050424213 8708159830511452596113635)
          ·
            refine ⟨13062239745767178894170453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708159830511452596113635 13062239745767178894170453)
            ·
              refine ⟨38268280505177281916515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13062239745767178894170453 38268280505177281916515)
              ·
                rfl

theorem cell22_3018352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 10].length) (baseStart_3018352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018352 prefixEnd_3018352 := by exact prefixLift 3018352
  have htrace : WordTrace (prefixWord ++ tailWord_3018352) baseStart_3018352 baseEnd_3018352 := by
    simpa [prefixWord, tailWord_3018352, baseEnd_3018352] using wordTrace_append hprefix tailTrace_3018352
  have hstable : (prefixWord ++ tailWord_3018352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018352).length < 2 ^ (prefixWord ++ tailWord_3018352).sum := by decide
  have hdescent : baseEnd_3018352 < baseStart_3018352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018354 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_3018354 : Nat := 118140960795 + 3018354 * 2 ^ 59
def prefixEnd_3018354 : Nat := 4983230072969 + 3 ^ 40 * 3018354 * 2
def baseEnd_3018354 : Nat := 1033244258280659273195899

theorem tailTrace_3018354 : CollatzResearch.WordTrace tailWord_3018354 prefixEnd_3018354 1033244258280659273195899 := by
  unfold tailWord_3018354
  simp only [CollatzResearch.WordTrace]
  refine ⟨27522103626756606666937529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73392276338017617778500077 27522103626756606666937529)
  ·
    refine ⟨20641577720067455000203147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27522103626756606666937529 20641577720067455000203147)
    ·
      refine ⟨30962366580101182500304721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20641577720067455000203147 30962366580101182500304721)
      ·
        refine ⟨23221774935075886875228541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30962366580101182500304721 23221774935075886875228541)
        ·
          refine ⟨8708165600653457578210703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23221774935075886875228541 8708165600653457578210703)
          ·
            refine ⟨13062248400980186367316055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708165600653457578210703 13062248400980186367316055)
            ·
              refine ⟨19593372601470279550974083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062248400980186367316055 19593372601470279550974083)
              ·
                refine ⟨29390058902205419326461125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19593372601470279550974083 29390058902205419326461125)
                ·
                  refine ⟨5510636044163516123711461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29390058902205419326461125 5510636044163516123711461)
                  ·
                    refine ⟨1033244258280659273195899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5510636044163516123711461 1033244258280659273195899)
                    ·
                      rfl

theorem cell22_3018354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_3018354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018354 prefixEnd_3018354 := by exact prefixLift 3018354
  have htrace : WordTrace (prefixWord ++ tailWord_3018354) baseStart_3018354 baseEnd_3018354 := by
    simpa [prefixWord, tailWord_3018354, baseEnd_3018354] using wordTrace_append hprefix tailTrace_3018354
  have hstable : (prefixWord ++ tailWord_3018354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018354).length < 2 ^ (prefixWord ++ tailWord_3018354).sum := by decide
  have hdescent : baseEnd_3018354 < baseStart_3018354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018369 : List Nat := [1, 2, 4, 2, 1, 3, 2, 7]
def baseStart_3018369 : Nat := 118140960795 + 3018369 * 2 ^ 59
def prefixEnd_3018369 : Nat := 4983230072969 + 3 ^ 40 * 3018369 * 2
def baseEnd_3018369 : Nat := 114805488120800470452317

theorem tailTrace_3018369 : CollatzResearch.WordTrace tailWord_3018369 prefixEnd_3018369 114805488120800470452317 := by
  unfold tailWord_3018369
  simp only [CollatzResearch.WordTrace]
  refine ⟨110088961601972084229546161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73392641067981389486364107 110088961601972084229546161)
  ·
    refine ⟨82566721201479063172159621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110088961601972084229546161 82566721201479063172159621)
    ·
      refine ⟨15481260225277324344779929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82566721201479063172159621 15481260225277324344779929)
      ·
        refine ⟨11610945168957993258584947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15481260225277324344779929 11610945168957993258584947)
        ·
          refine ⟨17416417753436989887877421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11610945168957993258584947 17416417753436989887877421)
          ·
            refine ⟨6531156657538871207954033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17416417753436989887877421 6531156657538871207954033)
            ·
              refine ⟨4898367493154153405965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6531156657538871207954033 4898367493154153405965525)
              ·
                refine ⟨114805488120800470452317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4898367493154153405965525 114805488120800470452317)
                ·
                  rfl

theorem cell22_3018369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 7].length) (baseStart_3018369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018369 prefixEnd_3018369 := by exact prefixLift 3018369
  have htrace : WordTrace (prefixWord ++ tailWord_3018369) baseStart_3018369 baseEnd_3018369 := by
    simpa [prefixWord, tailWord_3018369, baseEnd_3018369] using wordTrace_append hprefix tailTrace_3018369
  have hstable : (prefixWord ++ tailWord_3018369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018369).length < 2 ^ (prefixWord ++ tailWord_3018369).sum := by decide
  have hdescent : baseEnd_3018369 < baseStart_3018369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018384 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 3, 3]
def baseStart_3018384 : Nat := 118140960795 + 3018384 * 2 ^ 59
def prefixEnd_3018384 : Nat := 4983230072969 + 3 ^ 40 * 3018384 * 2
def baseEnd_3018384 : Nat := 1033254527893749194945807

theorem tailTrace_3018384 : CollatzResearch.WordTrace tailWord_3018384 prefixEnd_3018384 1033254527893749194945807 := by
  unfold tailWord_3018384
  simp only [CollatzResearch.WordTrace]
  refine ⟨55044754348458870895671103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73393005797945161194228137 55044754348458870895671103)
  ·
    refine ⟨82567131522688306343506655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55044754348458870895671103 82567131522688306343506655)
    ·
      refine ⟨123850697284032459515259983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82567131522688306343506655 123850697284032459515259983)
      ·
        refine ⟨185776045926048689272889975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123850697284032459515259983 185776045926048689272889975)
        ·
          refine ⟨278664068889073033909334963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185776045926048689272889975 278664068889073033909334963)
          ·
            refine ⟨417996103333609550864002445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278664068889073033909334963 417996103333609550864002445)
            ·
              refine ⟨156748538750103581574000917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417996103333609550864002445 156748538750103581574000917)
              ·
                refine ⟨7347587753911105386281293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156748538750103581574000917 7347587753911105386281293)
                ·
                  refine ⟨2755345407716664519855485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7347587753911105386281293 2755345407716664519855485)
                  ·
                    refine ⟨1033254527893749194945807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2755345407716664519855485 1033254527893749194945807)
                    ·
                      rfl

theorem cell22_3018384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_3018384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018384 prefixEnd_3018384 := by exact prefixLift 3018384
  have htrace : WordTrace (prefixWord ++ tailWord_3018384) baseStart_3018384 baseEnd_3018384 := by
    simpa [prefixWord, tailWord_3018384, baseEnd_3018384] using wordTrace_append hprefix tailTrace_3018384
  have hstable : (prefixWord ++ tailWord_3018384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018384).length < 2 ^ (prefixWord ++ tailWord_3018384).sum := by decide
  have hdescent : baseEnd_3018384 < baseStart_3018384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018388 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3018388 : Nat := 118140960795 + 3018388 * 2 ^ 59
def prefixEnd_3018388 : Nat := 4983230072969 + 3 ^ 40 * 3018388 * 2
def baseEnd_3018388 : Nat := 1033255897175494517845795

theorem tailTrace_3018388 : CollatzResearch.WordTrace tailWord_3018388 prefixEnd_3018388 1033255897175494517845795 := by
  unfold tailWord_3018388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55044827294451625237243909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73393103059268833649658545 55044827294451625237243909)
  ·
    refine ⟨10320905117709679731983233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55044827294451625237243909 10320905117709679731983233)
    ·
      refine ⟨7740678838282259798987425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10320905117709679731983233 7740678838282259798987425)
      ·
        refine ⟨5805509128711694849240569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7740678838282259798987425 5805509128711694849240569)
        ·
          refine ⟨4354131846533771136930427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5805509128711694849240569 4354131846533771136930427)
          ·
            refine ⟨6531197769800656705395641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354131846533771136930427 6531197769800656705395641)
            ·
              refine ⟨4898398327350492529046731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6531197769800656705395641 4898398327350492529046731)
              ·
                refine ⟨7347597491025738793570097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898398327350492529046731 7347597491025738793570097)
                ·
                  refine ⟨5510698118269304095177573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7347597491025738793570097 5510698118269304095177573)
                  ·
                    refine ⟨1033255897175494517845795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5510698118269304095177573 1033255897175494517845795)
                    ·
                      rfl

theorem cell22_3018388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3018388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018388 prefixEnd_3018388 := by exact prefixLift 3018388
  have htrace : WordTrace (prefixWord ++ tailWord_3018388) baseStart_3018388 baseEnd_3018388 := by
    simpa [prefixWord, tailWord_3018388, baseEnd_3018388] using wordTrace_append hprefix tailTrace_3018388
  have hstable : (prefixWord ++ tailWord_3018388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018388).length < 2 ^ (prefixWord ++ tailWord_3018388).sum := by decide
  have hdescent : baseEnd_3018388 < baseStart_3018388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018412 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_3018412 : Nat := 118140960795 + 3018412 * 2 ^ 59
def prefixEnd_3018412 : Nat := 4983230072969 + 3 ^ 40 * 3018412 * 2
def baseEnd_3018412 : Nat := 1033264112865966455245721

theorem tailTrace_3018412 : CollatzResearch.WordTrace tailWord_3018412 prefixEnd_3018412 1033264112865966455245721 := by
  unfold tailWord_3018412
  simp only [CollatzResearch.WordTrace]
  refine ⟨55045264970408151286680745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73393686627210868382240993 55045264970408151286680745)
  ·
    refine ⟨41283948727806113465010559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55045264970408151286680745 41283948727806113465010559)
    ·
      refine ⟨61925923091709170197515839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41283948727806113465010559 61925923091709170197515839)
      ·
        refine ⟨92888884637563755296273759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61925923091709170197515839 92888884637563755296273759)
        ·
          refine ⟨139333326956345632944410639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92888884637563755296273759 139333326956345632944410639)
          ·
            refine ⟨208999990434518449416615959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139333326956345632944410639 208999990434518449416615959)
            ·
              refine ⟨313499985651777674124923939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208999990434518449416615959 313499985651777674124923939)
              ·
                refine ⟨470249978477666511187385909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313499985651777674124923939 470249978477666511187385909)
                ·
                  refine ⟨44085935482281235423817429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 470249978477666511187385909 44085935482281235423817429)
                  ·
                    refine ⟨1033264112865966455245721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44085935482281235423817429 1033264112865966455245721)
                    ·
                      rfl

theorem cell22_3018412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_3018412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018412 prefixEnd_3018412 := by exact prefixLift 3018412
  have htrace : WordTrace (prefixWord ++ tailWord_3018412) baseStart_3018412 baseEnd_3018412 := by
    simpa [prefixWord, tailWord_3018412, baseEnd_3018412] using wordTrace_append hprefix tailTrace_3018412
  have hstable : (prefixWord ++ tailWord_3018412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018412).length < 2 ^ (prefixWord ++ tailWord_3018412).sum := by decide
  have hdescent : baseEnd_3018412 < baseStart_3018412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018429 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_3018429 : Nat := 118140960795 + 3018429 * 2 ^ 59
def prefixEnd_3018429 : Nat := 4983230072969 + 3 ^ 40 * 3018429 * 2
def baseEnd_3018429 : Nat := 1033269932313384077570669

theorem tailTrace_3018429 : CollatzResearch.WordTrace tailWord_3018429 prefixEnd_3018429 1033269932313384077570669 := by
  unfold tailWord_3018429
  simp only [CollatzResearch.WordTrace]
  refine ⟨110091149981754714476730341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73394099987836476317820227 110091149981754714476730341)
  ·
    refine ⟨20642090621579008964386939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110091149981754714476730341 20642090621579008964386939)
    ·
      refine ⟨30963135932368513446580409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20642090621579008964386939 30963135932368513446580409)
      ·
        refine ⟨23222351949276385084935307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30963135932368513446580409 23222351949276385084935307)
        ·
          refine ⟨34833527923914577627402961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23222351949276385084935307 34833527923914577627402961)
          ·
            refine ⟨26125145942935933220552221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34833527923914577627402961 26125145942935933220552221)
            ·
              refine ⟨9796929728600974957707083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26125145942935933220552221 9796929728600974957707083)
              ·
                refine ⟨14695394592901462436560625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796929728600974957707083 14695394592901462436560625)
                ·
                  refine ⟨11021545944676096827420469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14695394592901462436560625 11021545944676096827420469)
                  ·
                    refine ⟨1033269932313384077570669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11021545944676096827420469 1033269932313384077570669)
                    ·
                      rfl

theorem cell22_3018429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_3018429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018429 prefixEnd_3018429 := by exact prefixLift 3018429
  have htrace : WordTrace (prefixWord ++ tailWord_3018429) baseStart_3018429 baseEnd_3018429 := by
    simpa [prefixWord, tailWord_3018429, baseEnd_3018429] using wordTrace_append hprefix tailTrace_3018429
  have hstable : (prefixWord ++ tailWord_3018429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018429).length < 2 ^ (prefixWord ++ tailWord_3018429).sum := by decide
  have hdescent : baseEnd_3018429 < baseStart_3018429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018474 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3018474 : Nat := 118140960795 + 3018474 * 2 ^ 59
def prefixEnd_3018474 : Nat := 4983230072969 + 3 ^ 40 * 3018474 * 2
def baseEnd_3018474 : Nat := 1033285336733018960195531

theorem tailTrace_3018474 : CollatzResearch.WordTrace tailWord_3018474 prefixEnd_3018474 1033285336733018960195531 := by
  unfold tailWord_3018474
  simp only [CollatzResearch.WordTrace]
  refine ⟨27523197816647921790529619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73395194177727791441412317 27523197816647921790529619)
  ·
    refine ⟨41284796724971882685794429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27523197816647921790529619 41284796724971882685794429)
    ·
      refine ⟨15481798771864456007172911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41284796724971882685794429 15481798771864456007172911)
      ·
        refine ⟨23222698157796684010759367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15481798771864456007172911 23222698157796684010759367)
        ·
          refine ⟨34834047236695026016139051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23222698157796684010759367 34834047236695026016139051)
          ·
            refine ⟨52251070855042539024208577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34834047236695026016139051 52251070855042539024208577)
            ·
              refine ⟨39188303141281904268156433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52251070855042539024208577 39188303141281904268156433)
              ·
                refine ⟨29391227355961428201117325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39188303141281904268156433 29391227355961428201117325)
                ·
                  refine ⟨11021710258485535575418997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29391227355961428201117325 11021710258485535575418997)
                  ·
                    refine ⟨1033285336733018960195531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11021710258485535575418997 1033285336733018960195531)
                    ·
                      rfl

theorem cell22_3018474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3018474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018474 prefixEnd_3018474 := by exact prefixLift 3018474
  have htrace : WordTrace (prefixWord ++ tailWord_3018474) baseStart_3018474 baseEnd_3018474 := by
    simpa [prefixWord, tailWord_3018474, baseEnd_3018474] using wordTrace_append hprefix tailTrace_3018474
  have hstable : (prefixWord ++ tailWord_3018474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018474).length < 2 ^ (prefixWord ++ tailWord_3018474).sum := by decide
  have hdescent : baseEnd_3018474 < baseStart_3018474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018476 : List Nat := [2, 2, 1, 1, 2, 2, 4, 4, 4]
def baseStart_3018476 : Nat := 118140960795 + 3018476 * 2 ^ 59
def prefixEnd_3018476 : Nat := 4983230072969 + 3 ^ 40 * 3018476 * 2
def baseEnd_3018476 : Nat := 344428673791297207215175

theorem tailTrace_3018476 : CollatzResearch.WordTrace tailWord_3018476 prefixEnd_3018476 344428673791297207215175 := by
  unfold tailWord_3018476
  simp only [CollatzResearch.WordTrace]
  refine ⟨55046432106292220751845641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73395242808389627669127521 55046432106292220751845641)
  ·
    refine ⟨41284824079719165563884231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55046432106292220751845641 41284824079719165563884231)
    ·
      refine ⟨61927236119578748345826347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41284824079719165563884231 61927236119578748345826347)
      ·
        refine ⟨92890854179368122518739521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61927236119578748345826347 92890854179368122518739521)
        ·
          refine ⟨69668140634526091889054641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92890854179368122518739521 69668140634526091889054641)
          ·
            refine ⟨52251105475894568916790981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69668140634526091889054641 52251105475894568916790981)
            ·
              refine ⟨9797082276730231671898309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52251105475894568916790981 9797082276730231671898309)
              ·
                refine ⟨1836952926886918438480933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9797082276730231671898309 1836952926886918438480933)
                ·
                  refine ⟨344428673791297207215175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836952926886918438480933 344428673791297207215175)
                  ·
                    rfl

theorem cell22_3018476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_3018476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018476 prefixEnd_3018476 := by exact prefixLift 3018476
  have htrace : WordTrace (prefixWord ++ tailWord_3018476) baseStart_3018476 baseEnd_3018476 := by
    simpa [prefixWord, tailWord_3018476, baseEnd_3018476] using wordTrace_append hprefix tailTrace_3018476
  have hstable : (prefixWord ++ tailWord_3018476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018476).length < 2 ^ (prefixWord ++ tailWord_3018476).sum := by decide
  have hdescent : baseEnd_3018476 < baseStart_3018476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018504 : List Nat := [2, 1, 3, 2, 2, 1, 3, 8]
def baseStart_3018504 : Nat := 118140960795 + 3018504 * 2 ^ 59
def prefixEnd_3018504 : Nat := 4983230072969 + 3 ^ 40 * 3018504 * 2
def baseEnd_3018504 : Nat := 114810622927345431327271

theorem tailTrace_3018504 : CollatzResearch.WordTrace tailWord_3018504 prefixEnd_3018504 114810622927345431327271 := by
  unfold tailWord_3018504
  simp only [CollatzResearch.WordTrace]
  refine ⟨55046942728241501142855283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73395923637655334857140377 55046942728241501142855283)
  ·
    refine ⟨82570414092362251714282925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55046942728241501142855283 82570414092362251714282925)
    ·
      refine ⟨30963905284635844392856097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82570414092362251714282925 30963905284635844392856097)
      ·
        refine ⟨23222928963476883294642073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30963905284635844392856097 23222928963476883294642073)
        ·
          refine ⟨17417196722607662470981555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23222928963476883294642073 17417196722607662470981555)
          ·
            refine ⟨26125795083911493706472333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17417196722607662470981555 26125795083911493706472333)
            ·
              refine ⟨9797173156466810139927125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26125795083911493706472333 9797173156466810139927125)
              ·
                refine ⟨114810622927345431327271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9797173156466810139927125 114810622927345431327271)
                ·
                  rfl

theorem cell22_3018504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 8].length) (baseStart_3018504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018504 prefixEnd_3018504 := by exact prefixLift 3018504
  have htrace : WordTrace (prefixWord ++ tailWord_3018504) baseStart_3018504 baseEnd_3018504 := by
    simpa [prefixWord, tailWord_3018504, baseEnd_3018504] using wordTrace_append hprefix tailTrace_3018504
  have hstable : (prefixWord ++ tailWord_3018504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018504).length < 2 ^ (prefixWord ++ tailWord_3018504).sum := by decide
  have hdescent : baseEnd_3018504 < baseStart_3018504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018583 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 5]
def baseStart_3018583 : Nat := 118140960795 + 3018583 * 2 ^ 59
def prefixEnd_3018583 : Nat := 4983230072969 + 3 ^ 40 * 3018583 * 2
def baseEnd_3018583 : Nat := 344440883220193003073399

theorem tailTrace_3018583 : CollatzResearch.WordTrace tailWord_3018583 prefixEnd_3018583 344440883220193003073399 := by
  unfold tailWord_3018583
  simp only [CollatzResearch.WordTrace]
  refine ⟨110096766823196798777836403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73397844548797865851890935 110096766823196798777836403)
  ·
    refine ⟨165145150234795198166754605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110096766823196798777836403 165145150234795198166754605)
    ·
      refine ⟨61929431338048199312532977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165145150234795198166754605 61929431338048199312532977)
      ·
        refine ⟨46447073503536149484399733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61929431338048199312532977 46447073503536149484399733)
        ·
          refine ⟨4354413140956514014162475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46447073503536149484399733 4354413140956514014162475)
          ·
            refine ⟨6531619711434771021243713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354413140956514014162475 6531619711434771021243713)
            ·
              refine ⟨4898714783576078265932785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6531619711434771021243713 4898714783576078265932785)
              ·
                refine ⟨3674036087682058699449589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4898714783576078265932785 3674036087682058699449589)
                ·
                  refine ⟨344440883220193003073399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3674036087682058699449589 344440883220193003073399)
                  ·
                    rfl

theorem cell22_3018583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 5].length) (baseStart_3018583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018583 prefixEnd_3018583 := by exact prefixLift 3018583
  have htrace : WordTrace (prefixWord ++ tailWord_3018583) baseStart_3018583 baseEnd_3018583 := by
    simpa [prefixWord, tailWord_3018583, baseEnd_3018583] using wordTrace_append hprefix tailTrace_3018583
  have hstable : (prefixWord ++ tailWord_3018583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018583).length < 2 ^ (prefixWord ++ tailWord_3018583).sum := by decide
  have hdescent : baseEnd_3018583 < baseStart_3018583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018613 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3018613 : Nat := 118140960795 + 3018613 * 2 ^ 59
def prefixEnd_3018613 : Nat := 4983230072969 + 3 ^ 40 * 3018613 * 2
def baseEnd_3018613 : Nat := 1033332919273668930970105

theorem tailTrace_3018613 : CollatzResearch.WordTrace tailWord_3018613 prefixEnd_3018613 1033332919273668930970105 := by
  unfold tailWord_3018613
  simp only [CollatzResearch.WordTrace]
  refine ⟨110097861013088113901428493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73398574008725409267618995 110097861013088113901428493)
  ·
    refine ⟨41286697879908042713035685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110097861013088113901428493 41286697879908042713035685)
    ·
      refine ⟨7741255852482758008694191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41286697879908042713035685 7741255852482758008694191)
      ·
        refine ⟨11611883778724137013041287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7741255852482758008694191 11611883778724137013041287)
        ·
          refine ⟨17417825668086205519561931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11611883778724137013041287 17417825668086205519561931)
          ·
            refine ⟨26126738502129308279342897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17417825668086205519561931 26126738502129308279342897)
            ·
              refine ⟨19595053876596981209507173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26126738502129308279342897 19595053876596981209507173)
              ·
                refine ⟨3674072601861933976782595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19595053876596981209507173 3674072601861933976782595)
                ·
                  refine ⟨5511108902792900965173893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674072601861933976782595 5511108902792900965173893)
                  ·
                    refine ⟨1033332919273668930970105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5511108902792900965173893 1033332919273668930970105)
                    ·
                      rfl

theorem cell22_3018613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3018613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018613 prefixEnd_3018613 := by exact prefixLift 3018613
  have htrace : WordTrace (prefixWord ++ tailWord_3018613) baseStart_3018613 baseEnd_3018613 := by
    simpa [prefixWord, tailWord_3018613, baseEnd_3018613] using wordTrace_append hprefix tailTrace_3018613
  have hstable : (prefixWord ++ tailWord_3018613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018613).length < 2 ^ (prefixWord ++ tailWord_3018613).sum := by decide
  have hdescent : baseEnd_3018613 < baseStart_3018613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018628 : List Nat := [2, 3, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3018628 : Nat := 118140960795 + 3018628 * 2 ^ 59
def prefixEnd_3018628 : Nat := 4983230072969 + 3 ^ 40 * 3018628 * 2
def baseEnd_3018628 : Nat := 344446018026737963948353

theorem tailTrace_3018628 : CollatzResearch.WordTrace tailWord_3018628 prefixEnd_3018628 344446018026737963948353 := by
  unfold tailWord_3018628
  simp only [CollatzResearch.WordTrace]
  refine ⟨55049204054016885731612269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73398938738689180975483025 55049204054016885731612269)
  ·
    refine ⟨20643451520256332149354601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55049204054016885731612269 20643451520256332149354601)
    ·
      refine ⟨15482588640192249112015951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20643451520256332149354601 15482588640192249112015951)
      ·
        refine ⟨23223882960288373668023927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15482588640192249112015951 23223882960288373668023927)
        ·
          refine ⟨34835824440432560502035891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23223882960288373668023927 34835824440432560502035891)
          ·
            refine ⟨52253736660648840753053837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34835824440432560502035891 52253736660648840753053837)
            ·
              refine ⟨19595151247743315282395189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52253736660648840753053837 19595151247743315282395189)
              ·
                refine ⟨1837045429475935807724549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19595151247743315282395189 1837045429475935807724549)
                ·
                  refine ⟨344446018026737963948353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837045429475935807724549 344446018026737963948353)
                  ·
                    rfl

theorem cell22_3018628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3018628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018628 prefixEnd_3018628 := by exact prefixLift 3018628
  have htrace : WordTrace (prefixWord ++ tailWord_3018628) baseStart_3018628 baseEnd_3018628 := by
    simpa [prefixWord, tailWord_3018628, baseEnd_3018628] using wordTrace_append hprefix tailTrace_3018628
  have hstable : (prefixWord ++ tailWord_3018628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018628).length < 2 ^ (prefixWord ++ tailWord_3018628).sum := by decide
  have hdescent : baseEnd_3018628 < baseStart_3018628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018641 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_3018641 : Nat := 118140960795 + 3018641 * 2 ^ 59
def prefixEnd_3018641 : Nat := 4983230072969 + 3 ^ 40 * 3018641 * 2
def baseEnd_3018641 : Nat := 1033342504245886191270019

theorem tailTrace_3018641 : CollatzResearch.WordTrace tailWord_3018641 prefixEnd_3018641 1033342504245886191270019 := by
  unfold tailWord_3018641
  simp only [CollatzResearch.WordTrace]
  refine ⟨110098882256986674683447777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73399254837991116455631851 110098882256986674683447777)
  ·
    refine ⟨82574161692740006012585833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110098882256986674683447777 82574161692740006012585833)
    ·
      refine ⟨61930621269555004509439375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82574161692740006012585833 61930621269555004509439375)
      ·
        refine ⟨92895931904332506764159063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61930621269555004509439375 92895931904332506764159063)
        ·
          refine ⟨139343897856498760146238595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92895931904332506764159063 139343897856498760146238595)
          ·
            refine ⟨209015846784748140219357893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139343897856498760146238595 209015846784748140219357893)
            ·
              refine ⟨39190471272140276291129605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209015846784748140219357893 39190471272140276291129605)
              ·
                refine ⟨7348213363526301804586801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39190471272140276291129605 7348213363526301804586801)
                ·
                  refine ⟨5511160022644726353440101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348213363526301804586801 5511160022644726353440101)
                  ·
                    refine ⟨1033342504245886191270019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5511160022644726353440101 1033342504245886191270019)
                    ·
                      rfl

theorem cell22_3018641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_3018641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018641 prefixEnd_3018641 := by exact prefixLift 3018641
  have htrace : WordTrace (prefixWord ++ tailWord_3018641) baseStart_3018641 baseEnd_3018641 := by
    simpa [prefixWord, tailWord_3018641, baseEnd_3018641] using wordTrace_append hprefix tailTrace_3018641
  have hstable : (prefixWord ++ tailWord_3018641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018641).length < 2 ^ (prefixWord ++ tailWord_3018641).sum := by decide
  have hdescent : baseEnd_3018641 < baseStart_3018641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018673 : List Nat := [1, 2, 2, 4, 2, 1, 4, 6]
def baseStart_3018673 : Nat := 118140960795 + 3018673 * 2 ^ 59
def prefixEnd_3018673 : Nat := 4983230072969 + 3 ^ 40 * 3018673 * 2
def baseEnd_3018673 : Nat := 114817050944427641607769

theorem tailTrace_3018673 : CollatzResearch.WordTrace tailWord_3018673 prefixEnd_3018673 114817050944427641607769 := by
  unfold tailWord_3018673
  simp only [CollatzResearch.WordTrace]
  refine ⟨110100049392870744148612673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73400032928580496099075115 110100049392870744148612673)
  ·
    refine ⟨82575037044653058111459505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110100049392870744148612673 82575037044653058111459505)
    ·
      refine ⟨61931277783489793583594629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82575037044653058111459505 61931277783489793583594629)
      ·
        refine ⟨11612114584404336296923993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61931277783489793583594629 11612114584404336296923993)
        ·
          refine ⟨8709085938303252222692995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11612114584404336296923993 8709085938303252222692995)
          ·
            refine ⟨13063628907454878334039493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709085938303252222692995 13063628907454878334039493)
            ·
              refine ⟨2449430420147789687632405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13063628907454878334039493 2449430420147789687632405)
              ·
                refine ⟨114817050944427641607769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2449430420147789687632405 114817050944427641607769)
                ·
                  rfl

theorem cell22_3018673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 6].length) (baseStart_3018673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018673 prefixEnd_3018673 := by exact prefixLift 3018673
  have htrace : WordTrace (prefixWord ++ tailWord_3018673) baseStart_3018673 baseEnd_3018673 := by
    simpa [prefixWord, tailWord_3018673, baseEnd_3018673] using wordTrace_append hprefix tailTrace_3018673
  have hstable : (prefixWord ++ tailWord_3018673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018673).length < 2 ^ (prefixWord ++ tailWord_3018673).sum := by decide
  have hdescent : baseEnd_3018673 < baseStart_3018673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018778 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_3018778 : Nat := 118140960795 + 3018778 * 2 ^ 59
def prefixEnd_3018778 : Nat := 4983230072969 + 3 ^ 40 * 3018778 * 2
def baseEnd_3018778 : Nat := 1033389402145663500594599

theorem tailTrace_3018778 : CollatzResearch.WordTrace tailWord_3018778 prefixEnd_3018778 1033389402145663500594599 := by
  unfold tailWord_3018778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27525969764372586770296247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73402586038326898054123325 27525969764372586770296247)
  ·
    refine ⟨41288954646558880155444371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27525969764372586770296247 41288954646558880155444371)
    ·
      refine ⟨61933431969838320233166557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41288954646558880155444371 61933431969838320233166557)
      ·
        refine ⟨23225036988689370087437459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61933431969838320233166557 23225036988689370087437459)
        ·
          refine ⟨34837555483034055131156189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23225036988689370087437459 34837555483034055131156189)
          ·
            refine ⟨13064083306137770674183571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34837555483034055131156189 13064083306137770674183571)
            ·
              refine ⟨19596124959206656011275357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064083306137770674183571 19596124959206656011275357)
              ·
                refine ⟨7348546859702496004228259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19596124959206656011275357 7348546859702496004228259)
                ·
                  refine ⟨11022820289553744006342389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348546859702496004228259 11022820289553744006342389)
                  ·
                    refine ⟨1033389402145663500594599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11022820289553744006342389 1033389402145663500594599)
                    ·
                      rfl

theorem cell22_3018778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_3018778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018778 prefixEnd_3018778 := by exact prefixLift 3018778
  have htrace : WordTrace (prefixWord ++ tailWord_3018778) baseStart_3018778 baseEnd_3018778 := by
    simpa [prefixWord, tailWord_3018778, baseEnd_3018778] using wordTrace_append hprefix tailTrace_3018778
  have hstable : (prefixWord ++ tailWord_3018778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018778).length < 2 ^ (prefixWord ++ tailWord_3018778).sum := by decide
  have hdescent : baseEnd_3018778 < baseStart_3018778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018808 : List Nat := [2, 1, 2, 1, 6, 1, 9]
def baseStart_3018808 : Nat := 118140960795 + 3018808 * 2 ^ 59
def prefixEnd_3018808 : Nat := 4983230072969 + 3 ^ 40 * 3018808 * 2
def baseEnd_3018808 : Nat := 38274061916990867494241

theorem tailTrace_3018808 : CollatzResearch.WordTrace tailWord_3018808 prefixEnd_3018808 38274061916990867494241 := by
  unfold tailWord_3018808
  simp only [CollatzResearch.WordTrace]
  refine ⟨55052486623690831102388539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73403315498254441469851385 55052486623690831102388539)
  ·
    refine ⟨82578729935536246653582809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55052486623690831102388539 82578729935536246653582809)
    ·
      refine ⟨61934047451652184990187107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82578729935536246653582809 61934047451652184990187107)
      ·
        refine ⟨92901071177478277485280661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61934047451652184990187107 92901071177478277485280661)
        ·
          refine ⟨4354737711444294257122531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92901071177478277485280661 4354737711444294257122531)
          ·
            refine ⟨6532106567166441385683797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354737711444294257122531 6532106567166441385683797)
            ·
              refine ⟨38274061916990867494241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6532106567166441385683797 38274061916990867494241)
              ·
                rfl

theorem cell22_3018808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 9].length) (baseStart_3018808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018808 prefixEnd_3018808 := by exact prefixLift 3018808
  have htrace : WordTrace (prefixWord ++ tailWord_3018808) baseStart_3018808 baseEnd_3018808 := by
    simpa [prefixWord, tailWord_3018808, baseEnd_3018808] using wordTrace_append hprefix tailTrace_3018808
  have hstable : (prefixWord ++ tailWord_3018808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018808).length < 2 ^ (prefixWord ++ tailWord_3018808).sum := by decide
  have hdescent : baseEnd_3018808 < baseStart_3018808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018829 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3018829 : Nat := 118140960795 + 3018829 * 2 ^ 59
def prefixEnd_3018829 : Nat := 4983230072969 + 3 ^ 40 * 3018829 * 2
def baseEnd_3018829 : Nat := 1033406860487916367569443

theorem tailTrace_3018829 : CollatzResearch.WordTrace tailWord_3018829 prefixEnd_3018829 1033406860487916367569443 := by
  unfold tailWord_3018829
  simp only [CollatzResearch.WordTrace]
  refine ⟨110105739180305582791291541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73403826120203721860861027 110105739180305582791291541)
  ·
    refine ⟨5161206524076824193341791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110105739180305582791291541 5161206524076824193341791)
    ·
      refine ⟨7741809786115236290012687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5161206524076824193341791 7741809786115236290012687)
      ·
        refine ⟨11612714679172854435019031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7741809786115236290012687 11612714679172854435019031)
        ·
          refine ⟨17419072018759281652528547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11612714679172854435019031 17419072018759281652528547)
          ·
            refine ⟨26128608028138922478792821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17419072018759281652528547 26128608028138922478792821)
            ·
              refine ⟨2449557002638023982386827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26128608028138922478792821 2449557002638023982386827)
              ·
                refine ⟨3674335503957035973580241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449557002638023982386827 3674335503957035973580241)
                ·
                  refine ⟨2755751627967776980185181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3674335503957035973580241 2755751627967776980185181)
                  ·
                    refine ⟨1033406860487916367569443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2755751627967776980185181 1033406860487916367569443)
                    ·
                      rfl

theorem cell22_3018829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3018829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018829 prefixEnd_3018829 := by exact prefixLift 3018829
  have htrace : WordTrace (prefixWord ++ tailWord_3018829) baseStart_3018829 baseEnd_3018829 := by
    simpa [prefixWord, tailWord_3018829, baseEnd_3018829] using wordTrace_append hprefix tailTrace_3018829
  have hstable : (prefixWord ++ tailWord_3018829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018829).length < 2 ^ (prefixWord ++ tailWord_3018829).sum := by decide
  have hdescent : baseEnd_3018829 < baseStart_3018829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018840 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 3, 3]
def baseStart_3018840 : Nat := 118140960795 + 3018840 * 2 ^ 59
def prefixEnd_3018840 : Nat := 4983230072969 + 3 ^ 40 * 3018840 * 2
def baseEnd_3018840 : Nat := 1033410626012716005544409

theorem tailTrace_3018840 : CollatzResearch.WordTrace tailWord_3018840 prefixEnd_3018840 1033410626012716005544409 := by
  unfold tailWord_3018840
  simp only [CollatzResearch.WordTrace]
  refine ⟨55053070191632865834970987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73404093588843821113294649 55053070191632865834970987)
  ·
    refine ⟨82579605287449298752456481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55053070191632865834970987 82579605287449298752456481)
    ·
      refine ⟨61934703965586974064342361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82579605287449298752456481 61934703965586974064342361)
      ·
        refine ⟨46451027974190230548256771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61934703965586974064342361 46451027974190230548256771)
        ·
          refine ⟨69676541961285345822385157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46451027974190230548256771 69676541961285345822385157)
          ·
            refine ⟨13064351617741002341697217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69676541961285345822385157 13064351617741002341697217)
            ·
              refine ⟨9798263713305751756272913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13064351617741002341697217 9798263713305751756272913)
              ·
                refine ⟨7348697784979313817204685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9798263713305751756272913 7348697784979313817204685)
                ·
                  refine ⟨2755761669367242681451757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7348697784979313817204685 2755761669367242681451757)
                  ·
                    refine ⟨1033410626012716005544409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2755761669367242681451757 1033410626012716005544409)
                    ·
                      rfl

theorem cell22_3018840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_3018840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018840 prefixEnd_3018840 := by exact prefixLift 3018840
  have htrace : WordTrace (prefixWord ++ tailWord_3018840) baseStart_3018840 baseEnd_3018840 := by
    simpa [prefixWord, tailWord_3018840, baseEnd_3018840] using wordTrace_append hprefix tailTrace_3018840
  have hstable : (prefixWord ++ tailWord_3018840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018840).length < 2 ^ (prefixWord ++ tailWord_3018840).sum := by decide
  have hdescent : baseEnd_3018840 < baseStart_3018840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018853 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 7]
def baseStart_3018853 : Nat := 118140960795 + 3018853 * 2 ^ 59
def prefixEnd_3018853 : Nat := 4983230072969 + 3 ^ 40 * 3018853 * 2
def baseEnd_3018853 : Nat := 344471692059462768323123

theorem tailTrace_3018853 : CollatzResearch.WordTrace tailWord_3018853 prefixEnd_3018853 344471692059462768323123 := by
  unfold tailWord_3018853
  simp only [CollatzResearch.WordTrace]
  refine ⟨110106614532218634890165213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73404409688145756593443475 110106614532218634890165213)
  ·
    refine ⟨41289980449581988083811955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110106614532218634890165213 41289980449581988083811955)
    ·
      refine ⟨61934970674372982125717933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41289980449581988083811955 61934970674372982125717933)
      ·
        refine ⟨23225614002889868297144225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61934970674372982125717933 23225614002889868297144225)
        ·
          refine ⟨17419210502167401222858169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23225614002889868297144225 17419210502167401222858169)
          ·
            refine ⟨13064407876625550917143627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17419210502167401222858169 13064407876625550917143627)
            ·
              refine ⟨19596611814938326375715441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064407876625550917143627 19596611814938326375715441)
              ·
                refine ⟨14697458861203744781786581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19596611814938326375715441 14697458861203744781786581)
                ·
                  refine ⟨344471692059462768323123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14697458861203744781786581 344471692059462768323123)
                  ·
                    rfl

theorem cell22_3018853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_3018853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018853 prefixEnd_3018853 := by exact prefixLift 3018853
  have htrace : WordTrace (prefixWord ++ tailWord_3018853) baseStart_3018853 baseEnd_3018853 := by
    simpa [prefixWord, tailWord_3018853, baseEnd_3018853] using wordTrace_append hprefix tailTrace_3018853
  have hstable : (prefixWord ++ tailWord_3018853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018853).length < 2 ^ (prefixWord ++ tailWord_3018853).sum := by decide
  have hdescent : baseEnd_3018853 < baseStart_3018853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018870 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_3018870 : Nat := 118140960795 + 3018870 * 2 ^ 59
def prefixEnd_3018870 : Nat := 4983230072969 + 3 ^ 40 * 3018870 * 2
def baseEnd_3018870 : Nat := 344473631875268642431439

theorem tailTrace_3018870 : CollatzResearch.WordTrace tailWord_3018870 prefixEnd_3018870 344473631875268642431439 := by
  unfold tailWord_3018870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881702160822315424595879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73404823048771364529022709 6881702160822315424595879)
  ·
    refine ⟨10322553241233473136893819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6881702160822315424595879 10322553241233473136893819)
    ·
      refine ⟨15483829861850209705340729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10322553241233473136893819 15483829861850209705340729)
      ·
        refine ⟨11612872396387657279005547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15483829861850209705340729 11612872396387657279005547)
        ·
          refine ⟨17419308594581485918508321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11612872396387657279005547 17419308594581485918508321)
          ·
            refine ⟨13064481445936114438881241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17419308594581485918508321 13064481445936114438881241)
            ·
              refine ⟨9798361084452085829160931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13064481445936114438881241 9798361084452085829160931)
              ·
                refine ⟨14697541626678128743741397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9798361084452085829160931 14697541626678128743741397)
                ·
                  refine ⟨344473631875268642431439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14697541626678128743741397 344473631875268642431439)
                  ·
                    rfl

theorem cell22_3018870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_3018870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018870 prefixEnd_3018870 := by exact prefixLift 3018870
  have htrace : WordTrace (prefixWord ++ tailWord_3018870) baseStart_3018870 baseEnd_3018870 := by
    simpa [prefixWord, tailWord_3018870, baseEnd_3018870] using wordTrace_append hprefix tailTrace_3018870
  have hstable : (prefixWord ++ tailWord_3018870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018870).length < 2 ^ (prefixWord ++ tailWord_3018870).sum := by decide
  have hdescent : baseEnd_3018870 < baseStart_3018870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018917 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_3018917 : Nat := 118140960795 + 3018917 * 2 ^ 59
def prefixEnd_3018917 : Nat := 4983230072969 + 3 ^ 40 * 3018917 * 2
def baseEnd_3018917 : Nat := 1033436984686313471369173

theorem tailTrace_3018917 : CollatzResearch.WordTrace tailWord_3018917 prefixEnd_3018917 1033436984686313471369173 := by
  unfold tailWord_3018917
  simp only [CollatzResearch.WordTrace]
  refine ⟨110108948803986773820495005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73405965869324515880330003 110108948803986773820495005)
  ·
    refine ⟨41290855801495040182685627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110108948803986773820495005 41290855801495040182685627)
    ·
      refine ⟨61936283702242560274028441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41290855801495040182685627 61936283702242560274028441)
      ·
        refine ⟨46452212776681920205521331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61936283702242560274028441 46452212776681920205521331)
        ·
          refine ⟨69678319165022880308281997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46452212776681920205521331 69678319165022880308281997)
          ·
            refine ⟨26129369686883580115605749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69678319165022880308281997 26129369686883580115605749)
            ·
              refine ⟨2449628408145335635838039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26129369686883580115605749 2449628408145335635838039)
              ·
                refine ⟨3674442612218003453757059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449628408145335635838039 3674442612218003453757059)
                ·
                  refine ⟨5511663918327005180635589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674442612218003453757059 5511663918327005180635589)
                  ·
                    refine ⟨1033436984686313471369173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5511663918327005180635589 1033436984686313471369173)
                    ·
                      rfl

theorem cell22_3018917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_3018917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018917 prefixEnd_3018917 := by exact prefixLift 3018917
  have htrace : WordTrace (prefixWord ++ tailWord_3018917) baseStart_3018917 baseEnd_3018917 := by
    simpa [prefixWord, tailWord_3018917, baseEnd_3018917] using wordTrace_append hprefix tailTrace_3018917
  have hstable : (prefixWord ++ tailWord_3018917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018917).length < 2 ^ (prefixWord ++ tailWord_3018917).sum := by decide
  have hdescent : baseEnd_3018917 < baseStart_3018917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018962 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3018962 : Nat := 118140960795 + 3018962 * 2 ^ 59
def prefixEnd_3018962 : Nat := 4983230072969 + 3 ^ 40 * 3018962 * 2
def baseEnd_3018962 : Nat := 1033452389105948353994035

theorem tailTrace_3018962 : CollatzResearch.WordTrace tailWord_3018962 prefixEnd_3018962 1033452389105948353994035 := by
  unfold tailWord_3018962
  simp only [CollatzResearch.WordTrace]
  refine ⟨27527647522205936626470785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73407060059215831003922093 27527647522205936626470785)
  ·
    refine ⟨20645735641654452469853089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27527647522205936626470785 20645735641654452469853089)
    ·
      refine ⟨15484301731240839352389817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20645735641654452469853089 15484301731240839352389817)
      ·
        refine ⟨11613226298430629514292363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15484301731240839352389817 11613226298430629514292363)
        ·
          refine ⟨17419839447645944271438545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11613226298430629514292363 17419839447645944271438545)
          ·
            refine ⟨13064879585734458203578909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17419839447645944271438545 13064879585734458203578909)
            ·
              refine ⟨4899329844650421826342091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13064879585734458203578909 4899329844650421826342091)
              ·
                refine ⟨7348994766975632739513137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899329844650421826342091 7348994766975632739513137)
                ·
                  refine ⟨5511746075231724554634853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348994766975632739513137 5511746075231724554634853)
                  ·
                    refine ⟨1033452389105948353994035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5511746075231724554634853 1033452389105948353994035)
                    ·
                      rfl

theorem cell22_3018962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3018962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018962 prefixEnd_3018962 := by exact prefixLift 3018962
  have htrace : WordTrace (prefixWord ++ tailWord_3018962) baseStart_3018962 baseEnd_3018962 := by
    simpa [prefixWord, tailWord_3018962, baseEnd_3018962] using wordTrace_append hprefix tailTrace_3018962
  have hstable : (prefixWord ++ tailWord_3018962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018962).length < 2 ^ (prefixWord ++ tailWord_3018962).sum := by decide
  have hdescent : baseEnd_3018962 < baseStart_3018962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018966 : List Nat := [5, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_3018966 : Nat := 118140960795 + 3018966 * 2 ^ 59
def prefixEnd_3018966 : Nat := 4983230072969 + 3 ^ 40 * 3018966 * 2
def baseEnd_3018966 : Nat := 344484586129231225631341

theorem tailTrace_3018966 : CollatzResearch.WordTrace tailWord_3018966 prefixEnd_3018966 344484586129231225631341 := by
  unfold tailWord_3018966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881920998800578449314297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73407157320539503459352501 6881920998800578449314297)
  ·
    refine ⟨5161440749100433836985723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6881920998800578449314297 5161440749100433836985723)
    ·
      refine ⟨7742161123650650755478585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5161440749100433836985723 7742161123650650755478585)
      ·
        refine ⟨5806620842737988066608939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7742161123650650755478585 5806620842737988066608939)
        ·
          refine ⟨8709931264106982099913409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5806620842737988066608939 8709931264106982099913409)
          ·
            refine ⟨6532448448080236574935057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8709931264106982099913409 6532448448080236574935057)
            ·
              refine ⟨4899336336060177431201293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6532448448080236574935057 4899336336060177431201293)
              ·
                refine ⟨1837251126022566536700485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4899336336060177431201293 1837251126022566536700485)
                ·
                  refine ⟨344484586129231225631341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837251126022566536700485 344484586129231225631341)
                  ·
                    rfl

theorem cell22_3018966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_3018966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018966 prefixEnd_3018966 := by exact prefixLift 3018966
  have htrace : WordTrace (prefixWord ++ tailWord_3018966) baseStart_3018966 baseEnd_3018966 := by
    simpa [prefixWord, tailWord_3018966, baseEnd_3018966] using wordTrace_append hprefix tailTrace_3018966
  have hstable : (prefixWord ++ tailWord_3018966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018966).length < 2 ^ (prefixWord ++ tailWord_3018966).sum := by decide
  have hdescent : baseEnd_3018966 < baseStart_3018966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018975 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 7, 3]
def baseStart_3018975 : Nat := 118140960795 + 3018975 * 2 ^ 59
def prefixEnd_3018975 : Nat := 4983230072969 + 3 ^ 40 * 3018975 * 2
def baseEnd_3018975 : Nat := 1033456839271620653418995

theorem tailTrace_3018975 : CollatzResearch.WordTrace tailWord_3018975 prefixEnd_3018975 1033456839271620653418995 := by
  unfold tailWord_3018975
  simp only [CollatzResearch.WordTrace]
  refine ⟨110111064237776649726106379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73407376158517766484070919 110111064237776649726106379)
  ·
    refine ⟨165166596356664974589159569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110111064237776649726106379 165166596356664974589159569)
    ·
      refine ⟨123874947267498730941869677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165166596356664974589159569 123874947267498730941869677)
      ·
        refine ⟨46453105225312024103201129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123874947267498730941869677 46453105225312024103201129)
        ·
          refine ⟨34839828918984018077400847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46453105225312024103201129 34839828918984018077400847)
          ·
            refine ⟨52259743378476027116101271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34839828918984018077400847 52259743378476027116101271)
            ·
              refine ⟨78389615067714040674151907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52259743378476027116101271 78389615067714040674151907)
              ·
                refine ⟨117584422601571061011227861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78389615067714040674151907 117584422601571061011227861)
                ·
                  refine ⟨2755884904724321742450653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 117584422601571061011227861 2755884904724321742450653)
                  ·
                    refine ⟨1033456839271620653418995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2755884904724321742450653 1033456839271620653418995)
                    ·
                      rfl

theorem cell22_3018975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_3018975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3018975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3018975 prefixEnd_3018975 := by exact prefixLift 3018975
  have htrace : WordTrace (prefixWord ++ tailWord_3018975) baseStart_3018975 baseEnd_3018975 := by
    simpa [prefixWord, tailWord_3018975, baseEnd_3018975] using wordTrace_append hprefix tailTrace_3018975
  have hstable : (prefixWord ++ tailWord_3018975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018975).length < 2 ^ (prefixWord ++ tailWord_3018975).sum := by decide
  have hdescent : baseEnd_3018975 < baseStart_3018975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019005 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 5]
def baseStart_3019005 : Nat := 118140960795 + 3019005 * 2 ^ 59
def prefixEnd_3019005 : Nat := 4983230072969 + 3 ^ 40 * 3019005 * 2
def baseEnd_3019005 : Nat := 344489036294903525056301

theorem tailTrace_3019005 : CollatzResearch.WordTrace tailWord_3019005 prefixEnd_3019005 344489036294903525056301 := by
  unfold tailWord_3019005
  simp only [CollatzResearch.WordTrace]
  refine ⟨110112158427667964849698469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73408105618445309899798979 110112158427667964849698469)
  ·
    refine ⟨20646029705187743409318463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110112158427667964849698469 20646029705187743409318463)
    ·
      refine ⟨30969044557781615113977695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20646029705187743409318463 30969044557781615113977695)
      ·
        refine ⟨46453566836672422670966543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30969044557781615113977695 46453566836672422670966543)
        ·
          refine ⟨69680350255008634006449815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46453566836672422670966543 69680350255008634006449815)
          ·
            refine ⟨104520525382512951009674723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69680350255008634006449815 104520525382512951009674723)
            ·
              refine ⟨156780788073769426514512085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104520525382512951009674723 156780788073769426514512085)
              ·
                refine ⟨3674549720478970933933877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 156780788073769426514512085 3674549720478970933933877)
                ·
                  refine ⟨344489036294903525056301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3674549720478970933933877 344489036294903525056301)
                  ·
                    rfl

theorem cell22_3019005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_3019005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019005 prefixEnd_3019005 := by exact prefixLift 3019005
  have htrace : WordTrace (prefixWord ++ tailWord_3019005) baseStart_3019005 baseEnd_3019005 := by
    simpa [prefixWord, tailWord_3019005, baseEnd_3019005] using wordTrace_append hprefix tailTrace_3019005
  have hstable : (prefixWord ++ tailWord_3019005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019005).length < 2 ^ (prefixWord ++ tailWord_3019005).sum := by decide
  have hdescent : baseEnd_3019005 < baseStart_3019005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019080 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_3019080 : Nat := 118140960795 + 3019080 * 2 ^ 59
def prefixEnd_3019080 : Nat := 4983230072969 + 3 ^ 40 * 3019080 * 2
def baseEnd_3019080 : Nat := 1033492782917435379543673

theorem tailTrace_3019080 : CollatzResearch.WordTrace tailWord_3019080 prefixEnd_3019080 1033492782917435379543673 := by
  unfold tailWord_3019080
  simp only [CollatzResearch.WordTrace]
  refine ⟨55057446951198126329339347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73409929268264168439119129 55057446951198126329339347)
  ·
    refine ⟨82586170426797189494009021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55057446951198126329339347 82586170426797189494009021)
    ·
      refine ⟨30969813910048946060253383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82586170426797189494009021 30969813910048946060253383)
      ·
        refine ⟨46454720865073419090380075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30969813910048946060253383 46454720865073419090380075)
        ·
          refine ⟨69682081297610128635570113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46454720865073419090380075 69682081297610128635570113)
          ·
            refine ⟨52261560973207596476677585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69682081297610128635570113 52261560973207596476677585)
            ·
              refine ⟨39196170729905697357508189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52261560973207596476677585 39196170729905697357508189)
              ·
                refine ⟨14698564023714636509065571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39196170729905697357508189 14698564023714636509065571)
                ·
                  refine ⟨22047846035571954763598357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14698564023714636509065571 22047846035571954763598357)
                  ·
                    refine ⟨1033492782917435379543673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22047846035571954763598357 1033492782917435379543673)
                    ·
                      rfl

theorem cell22_3019080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_3019080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019080 prefixEnd_3019080 := by exact prefixLift 3019080
  have htrace : WordTrace (prefixWord ++ tailWord_3019080) baseStart_3019080 baseEnd_3019080 := by
    simpa [prefixWord, tailWord_3019080, baseEnd_3019080] using wordTrace_append hprefix tailTrace_3019080
  have hstable : (prefixWord ++ tailWord_3019080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019080).length < 2 ^ (prefixWord ++ tailWord_3019080).sum := by decide
  have hdescent : baseEnd_3019080 < baseStart_3019080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019112 : List Nat := [2, 1, 4, 2, 2, 1, 3, 7]
def baseStart_3019112 : Nat := 118140960795 + 3019112 * 2 ^ 59
def prefixEnd_3019112 : Nat := 4983230072969 + 3 ^ 40 * 3019112 * 2
def baseEnd_3019112 : Nat := 114833748574599773638175

theorem tailTrace_3019112 : CollatzResearch.WordTrace tailWord_3019112 prefixEnd_3019112 114833748574599773638175 := by
  unfold tailWord_3019112
  simp only [CollatzResearch.WordTrace]
  refine ⟨55058030519140161061921795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73410707358853548082562393 55058030519140161061921795)
  ·
    refine ⟨82587045778710241592882693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55058030519140161061921795 82587045778710241592882693)
    ·
      refine ⟨15485071083508170298665505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82587045778710241592882693 15485071083508170298665505)
      ·
        refine ⟨11613803312631127723999129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15485071083508170298665505 11613803312631127723999129)
        ·
          refine ⟨8710352484473345792999347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11613803312631127723999129 8710352484473345792999347)
          ·
            refine ⟨13065528726710018689499021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8710352484473345792999347 13065528726710018689499021)
            ·
              refine ⟨4899573272516257008562133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13065528726710018689499021 4899573272516257008562133)
              ·
                refine ⟨114833748574599773638175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4899573272516257008562133 114833748574599773638175)
                ·
                  rfl

theorem cell22_3019112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 7].length) (baseStart_3019112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019112 prefixEnd_3019112 := by exact prefixLift 3019112
  have htrace : WordTrace (prefixWord ++ tailWord_3019112) baseStart_3019112 baseEnd_3019112 := by
    simpa [prefixWord, tailWord_3019112, baseEnd_3019112] using wordTrace_append hprefix tailTrace_3019112
  have hstable : (prefixWord ++ tailWord_3019112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019112).length < 2 ^ (prefixWord ++ tailWord_3019112).sum := by decide
  have hdescent : baseEnd_3019112 < baseStart_3019112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019172 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_3019172 : Nat := 118140960795 + 3019172 * 2 ^ 59
def prefixEnd_3019172 : Nat := 4983230072969 + 3 ^ 40 * 3019172 * 2
def baseEnd_3019172 : Nat := 1033524276397577806243391

theorem tailTrace_3019172 : CollatzResearch.WordTrace tailWord_3019172 prefixEnd_3019172 1033524276397577806243391 := by
  unfold tailWord_3019172
  simp only [CollatzResearch.WordTrace]
  refine ⟨55059124709031476185513885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73412166278708634914018513 55059124709031476185513885)
  ·
    refine ⟨20647171765886803569567707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55059124709031476185513885 20647171765886803569567707)
    ·
      refine ⟨30970757648830205354351561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20647171765886803569567707 30970757648830205354351561)
      ·
        refine ⟨23228068236622654015763671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30970757648830205354351561 23228068236622654015763671)
        ·
          refine ⟨34842102354933981023645507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23228068236622654015763671 34842102354933981023645507)
          ·
            refine ⟨52263153532400971535468261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34842102354933981023645507 52263153532400971535468261)
            ·
              refine ⟨9799341287325182162900299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52263153532400971535468261 9799341287325182162900299)
              ·
                refine ⟨14699011930987773244350449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9799341287325182162900299 14699011930987773244350449)
                ·
                  refine ⟨11024258948240829933262837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14699011930987773244350449 11024258948240829933262837)
                  ·
                    refine ⟨1033524276397577806243391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11024258948240829933262837 1033524276397577806243391)
                    ·
                      rfl

theorem cell22_3019172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_3019172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019172 prefixEnd_3019172 := by exact prefixLift 3019172
  have htrace : WordTrace (prefixWord ++ tailWord_3019172) baseStart_3019172 baseEnd_3019172 := by
    simpa [prefixWord, tailWord_3019172, baseEnd_3019172] using wordTrace_append hprefix tailTrace_3019172
  have hstable : (prefixWord ++ tailWord_3019172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019172).length < 2 ^ (prefixWord ++ tailWord_3019172).sum := by decide
  have hdescent : baseEnd_3019172 < baseStart_3019172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019232 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_3019232 : Nat := 118140960795 + 3019232 * 2 ^ 59
def prefixEnd_3019232 : Nat := 4983230072969 + 3 ^ 40 * 3019232 * 2
def baseEnd_3019232 : Nat := 1033544815623757649743207

theorem tailTrace_3019232 : CollatzResearch.WordTrace tailWord_3019232 prefixEnd_3019232 1033544815623757649743207 := by
  unfold tailWord_3019232
  simp only [CollatzResearch.WordTrace]
  refine ⟨55060218898922791309105975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73413625198563721745474633 55060218898922791309105975)
  ·
    refine ⟨82590328348384186963658963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55060218898922791309105975 82590328348384186963658963)
    ·
      refine ⟨123885492522576280445488445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82590328348384186963658963 123885492522576280445488445)
      ·
        refine ⟨46457059695966105167058167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123885492522576280445488445 46457059695966105167058167)
        ·
          refine ⟨69685589543949157750587251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46457059695966105167058167 69685589543949157750587251)
          ·
            refine ⟨104528384315923736625880877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69685589543949157750587251 104528384315923736625880877)
            ·
              refine ⟨39198144118471401234705329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104528384315923736625880877 39198144118471401234705329)
              ·
                refine ⟨29398608088853550926028997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39198144118471401234705329 29398608088853550926028997)
                ·
                  refine ⟨5512239016660040798630437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29398608088853550926028997 5512239016660040798630437)
                  ·
                    refine ⟨1033544815623757649743207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5512239016660040798630437 1033544815623757649743207)
                    ·
                      rfl

theorem cell22_3019232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_3019232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019232 prefixEnd_3019232 := by exact prefixLift 3019232
  have htrace : WordTrace (prefixWord ++ tailWord_3019232) baseStart_3019232 baseEnd_3019232 := by
    simpa [prefixWord, tailWord_3019232, baseEnd_3019232] using wordTrace_append hprefix tailTrace_3019232
  have hstable : (prefixWord ++ tailWord_3019232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019232).length < 2 ^ (prefixWord ++ tailWord_3019232).sum := by decide
  have hdescent : baseEnd_3019232 < baseStart_3019232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019249 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_3019249 : Nat := 118140960795 + 3019249 * 2 ^ 59
def prefixEnd_3019249 : Nat := 4983230072969 + 3 ^ 40 * 3019249 * 2
def baseEnd_3019249 : Nat := 1033550635071175272068155

theorem tailTrace_3019249 : CollatzResearch.WordTrace tailWord_3019249 prefixEnd_3019249 1033550635071175272068155 := by
  unfold tailWord_3019249
  simp only [CollatzResearch.WordTrace]
  refine ⟨110121057838783994521580801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73414038559189329681053867 110121057838783994521580801)
  ·
    refine ⟨82590793379087995891185601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110121057838783994521580801 82590793379087995891185601)
    ·
      refine ⟨61943095034315996918389201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82590793379087995891185601 61943095034315996918389201)
      ·
        refine ⟨46457321275736997688791901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61943095034315996918389201 46457321275736997688791901)
        ·
          refine ⟨17421495478401374133296963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46457321275736997688791901 17421495478401374133296963)
          ·
            refine ⟨26132243217602061199945445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17421495478401374133296963 26132243217602061199945445)
            ·
              refine ⟨4899795603300386474989771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26132243217602061199945445 4899795603300386474989771)
              ·
                refine ⟨7349693404950579712484657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899795603300386474989771 7349693404950579712484657)
                ·
                  refine ⟨5512270053712934784363493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7349693404950579712484657 5512270053712934784363493)
                  ·
                    refine ⟨1033550635071175272068155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5512270053712934784363493 1033550635071175272068155)
                    ·
                      rfl

theorem cell22_3019249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_3019249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019249 prefixEnd_3019249 := by exact prefixLift 3019249
  have htrace : WordTrace (prefixWord ++ tailWord_3019249) baseStart_3019249 baseEnd_3019249 := by
    simpa [prefixWord, tailWord_3019249, baseEnd_3019249] using wordTrace_append hprefix tailTrace_3019249
  have hstable : (prefixWord ++ tailWord_3019249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019249).length < 2 ^ (prefixWord ++ tailWord_3019249).sum := by decide
  have hdescent : baseEnd_3019249 < baseStart_3019249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019268 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_3019268 : Nat := 118140960795 + 3019268 * 2 ^ 59
def prefixEnd_3019268 : Nat := 4983230072969 + 3 ^ 40 * 3019268 * 2
def baseEnd_3019268 : Nat := 1033557139159465555843097

theorem tailTrace_3019268 : CollatzResearch.WordTrace tailWord_3019268 prefixEnd_3019268 1033557139159465555843097 := by
  unfold tailWord_3019268
  simp only [CollatzResearch.WordTrace]
  refine ⟨55060875412857580383261229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73414500550476773844348305 55060875412857580383261229)
  ·
    refine ⟨20647828279821592643722961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55060875412857580383261229 20647828279821592643722961)
    ·
      refine ⟨15485871209866194482792221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20647828279821592643722961 15485871209866194482792221)
      ·
        refine ⟨5807201703699822931047083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15485871209866194482792221 5807201703699822931047083)
        ·
          refine ⟨8710802555549734396570625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5807201703699822931047083 8710802555549734396570625)
          ·
            refine ⟨6533101916662300797427969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8710802555549734396570625 6533101916662300797427969)
            ·
              refine ⟨4899826437496725598070977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533101916662300797427969 4899826437496725598070977)
              ·
                refine ⟨3674869828122544198553233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4899826437496725598070977 3674869828122544198553233)
                ·
                  refine ⟨2756152371091908148914925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3674869828122544198553233 2756152371091908148914925)
                  ·
                    refine ⟨1033557139159465555843097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2756152371091908148914925 1033557139159465555843097)
                    ·
                      rfl

theorem cell22_3019268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_3019268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019268 prefixEnd_3019268 := by exact prefixLift 3019268
  have htrace : WordTrace (prefixWord ++ tailWord_3019268) baseStart_3019268 baseEnd_3019268 := by
    simpa [prefixWord, tailWord_3019268, baseEnd_3019268] using wordTrace_append hprefix tailTrace_3019268
  have hstable : (prefixWord ++ tailWord_3019268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019268).length < 2 ^ (prefixWord ++ tailWord_3019268).sum := by decide
  have hdescent : baseEnd_3019268 < baseStart_3019268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019300 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_3019300 : Nat := 118140960795 + 3019300 * 2 ^ 59
def prefixEnd_3019300 : Nat := 4983230072969 + 3 ^ 40 * 3019300 * 2
def baseEnd_3019300 : Nat := 1033568093413428139042999

theorem tailTrace_3019300 : CollatzResearch.WordTrace tailWord_3019300 prefixEnd_3019300 1033568093413428139042999 := by
  unfold tailWord_3019300
  simp only [CollatzResearch.WordTrace]
  refine ⟨55061458980799615115843677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73415278641066153487791569 55061458980799615115843677)
  ·
    refine ⟨20648047117799855668441379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55061458980799615115843677 20648047117799855668441379)
    ·
      refine ⟨30972070676699783502662069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20648047117799855668441379 30972070676699783502662069)
      ·
        refine ⟨2903631625940604703374569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30972070676699783502662069 2903631625940604703374569)
        ·
          refine ⟨2177723719455453527530927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903631625940604703374569 2177723719455453527530927)
          ·
            refine ⟨3266585579183180291296391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177723719455453527530927 3266585579183180291296391)
            ·
              refine ⟨4899878368774770436944587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266585579183180291296391 4899878368774770436944587)
              ·
                refine ⟨7349817553162155655416881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899878368774770436944587 7349817553162155655416881)
                ·
                  refine ⟨5512363164871616741562661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7349817553162155655416881 5512363164871616741562661)
                  ·
                    refine ⟨1033568093413428139042999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5512363164871616741562661 1033568093413428139042999)
                    ·
                      rfl

theorem cell22_3019300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_3019300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019300 prefixEnd_3019300 := by exact prefixLift 3019300
  have htrace : WordTrace (prefixWord ++ tailWord_3019300) baseStart_3019300 baseEnd_3019300 := by
    simpa [prefixWord, tailWord_3019300, baseEnd_3019300] using wordTrace_append hprefix tailTrace_3019300
  have hstable : (prefixWord ++ tailWord_3019300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019300).length < 2 ^ (prefixWord ++ tailWord_3019300).sum := by decide
  have hdescent : baseEnd_3019300 < baseStart_3019300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019324 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_3019324 : Nat := 118140960795 + 3019324 * 2 ^ 59
def prefixEnd_3019324 : Nat := 4983230072969 + 3 ^ 40 * 3019324 * 2
def baseEnd_3019324 : Nat := 1033576309103900076442925

theorem tailTrace_3019324 : CollatzResearch.WordTrace tailWord_3019324 prefixEnd_3019324 1033576309103900076442925 := by
  unfold tailWord_3019324
  simp only [CollatzResearch.WordTrace]
  refine ⟨55061896656756141165280513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73415862209008188220374017 55061896656756141165280513)
  ·
    refine ⟨41296422492567105873960385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55061896656756141165280513 41296422492567105873960385)
    ·
      refine ⟨30972316869425329405470289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41296422492567105873960385 30972316869425329405470289)
      ·
        refine ⟨23229237652068997054102717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30972316869425329405470289 23229237652068997054102717)
        ·
          refine ⟨8710964119525873895288519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23229237652068997054102717 8710964119525873895288519)
          ·
            refine ⟨13066446179288810842932779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8710964119525873895288519 13066446179288810842932779)
            ·
              refine ⟨19599669268933216264399169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13066446179288810842932779 19599669268933216264399169)
              ·
                refine ⟨14699751951699912198299377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19599669268933216264399169 14699751951699912198299377)
                ·
                  refine ⟨11024813963774934148724533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14699751951699912198299377 11024813963774934148724533)
                  ·
                    refine ⟨1033576309103900076442925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11024813963774934148724533 1033576309103900076442925)
                    ·
                      rfl

theorem cell22_3019324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_3019324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019324 prefixEnd_3019324 := by exact prefixLift 3019324
  have htrace : WordTrace (prefixWord ++ tailWord_3019324) baseStart_3019324 baseEnd_3019324 := by
    simpa [prefixWord, tailWord_3019324, baseEnd_3019324] using wordTrace_append hprefix tailTrace_3019324
  have hstable : (prefixWord ++ tailWord_3019324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019324).length < 2 ^ (prefixWord ++ tailWord_3019324).sum := by decide
  have hdescent : baseEnd_3019324 < baseStart_3019324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019341 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3019341 : Nat := 118140960795 + 3019341 * 2 ^ 59
def prefixEnd_3019341 : Nat := 4983230072969 + 3 ^ 40 * 3019341 * 2
def baseEnd_3019341 : Nat := 1033582128551317698767873

theorem tailTrace_3019341 : CollatzResearch.WordTrace tailWord_3019341 prefixEnd_3019341 1033582128551317698767873 := by
  unfold tailWord_3019341
  simp only [CollatzResearch.WordTrace]
  refine ⟨110124413354450694233929877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73416275569633796155953251 110124413354450694233929877)
  ·
    refine ⟨5162081875989876292215463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110124413354450694233929877 5162081875989876292215463)
    ·
      refine ⟨7743122813984814438323195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5162081875989876292215463 7743122813984814438323195)
      ·
        refine ⟨11614684220977221657484793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7743122813984814438323195 11614684220977221657484793)
        ·
          refine ⟨8711013165732916243113595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11614684220977221657484793 8711013165732916243113595)
          ·
            refine ⟨13066519748599374364670393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8711013165732916243113595 13066519748599374364670393)
            ·
              refine ⟨9799889811449530773502795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13066519748599374364670393 9799889811449530773502795)
              ·
                refine ⟨14699834717174296160254193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9799889811449530773502795 14699834717174296160254193)
                ·
                  refine ⟨11024876037880722120190645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14699834717174296160254193 11024876037880722120190645)
                  ·
                    refine ⟨1033582128551317698767873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11024876037880722120190645 1033582128551317698767873)
                    ·
                      rfl

theorem cell22_3019341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3019341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019341 prefixEnd_3019341 := by exact prefixLift 3019341
  have htrace : WordTrace (prefixWord ++ tailWord_3019341) baseStart_3019341 baseEnd_3019341 := by
    simpa [prefixWord, tailWord_3019341, baseEnd_3019341] using wordTrace_append hprefix tailTrace_3019341
  have hstable : (prefixWord ++ tailWord_3019341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019341).length < 2 ^ (prefixWord ++ tailWord_3019341).sum := by decide
  have hdescent : baseEnd_3019341 < baseStart_3019341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019384 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_3019384 : Nat := 118140960795 + 3019384 * 2 ^ 59
def prefixEnd_3019384 : Nat := 4983230072969 + 3 ^ 40 * 3019384 * 2
def baseEnd_3019384 : Nat := 1033596848330079919942741

theorem tailTrace_3019384 : CollatzResearch.WordTrace tailWord_3019384 prefixEnd_3019384 1033596848330079919942741 := by
  unfold tailWord_3019384
  simp only [CollatzResearch.WordTrace]
  refine ⟨55062990846647456288872603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73417321128863275051830137 55062990846647456288872603)
  ·
    refine ⟨82594486269971184433308905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55062990846647456288872603 82594486269971184433308905)
    ·
      refine ⟨61945864702478388324981679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82594486269971184433308905 61945864702478388324981679)
      ·
        refine ⟨92918797053717582487472519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61945864702478388324981679 92918797053717582487472519)
        ·
          refine ⟨139378195580576373731208779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92918797053717582487472519 139378195580576373731208779)
          ·
            refine ⟨209067293370864560596813169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139378195580576373731208779 209067293370864560596813169)
            ·
              refine ⟨156800470028148420447609877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209067293370864560596813169 156800470028148420447609877)
              ·
                refine ⟨7350022032569457208481713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156800470028148420447609877 7350022032569457208481713)
                ·
                  refine ⟨5512516524427092906361285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7350022032569457208481713 5512516524427092906361285)
                  ·
                    refine ⟨1033596848330079919942741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5512516524427092906361285 1033596848330079919942741)
                    ·
                      rfl

theorem cell22_3019384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_3019384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019384 prefixEnd_3019384 := by exact prefixLift 3019384
  have htrace : WordTrace (prefixWord ++ tailWord_3019384) baseStart_3019384 baseEnd_3019384 := by
    simpa [prefixWord, tailWord_3019384, baseEnd_3019384] using wordTrace_append hprefix tailTrace_3019384
  have hstable : (prefixWord ++ tailWord_3019384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019384).length < 2 ^ (prefixWord ++ tailWord_3019384).sum := by decide
  have hdescent : baseEnd_3019384 < baseStart_3019384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019394 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3019394 : Nat := 118140960795 + 3019394 * 2 ^ 59
def prefixEnd_3019394 : Nat := 4983230072969 + 3 ^ 40 * 3019394 * 2
def baseEnd_3019394 : Nat := 344533423844814409064237

theorem tailTrace_3019394 : CollatzResearch.WordTrace tailWord_3019394 prefixEnd_3019394 344533423844814409064237 := by
  unfold tailWord_3019394
  simp only [CollatzResearch.WordTrace]
  refine ⟨27531586605814671071402309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73417564282172456190406157 27531586605814671071402309)
  ·
    refine ⟨5162172488590250825887933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27531586605814671071402309 5162172488590250825887933)
    ·
      refine ⟨1935814683221344059707975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5162172488590250825887933 1935814683221344059707975)
      ·
        refine ⟨2903722024832016089561963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935814683221344059707975 2903722024832016089561963)
        ·
          refine ⟨4355583037248024134342945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2903722024832016089561963 4355583037248024134342945)
          ·
            refine ⟨3266687277936018100757209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4355583037248024134342945 3266687277936018100757209)
            ·
              refine ⟨2450015458452013575567907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3266687277936018100757209 2450015458452013575567907)
              ·
                refine ⟨3675023187678020363351861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450015458452013575567907 3675023187678020363351861)
                ·
                  refine ⟨344533423844814409064237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3675023187678020363351861 344533423844814409064237)
                  ·
                    rfl

theorem cell22_3019394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3019394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019394 prefixEnd_3019394 := by exact prefixLift 3019394
  have htrace : WordTrace (prefixWord ++ tailWord_3019394) baseStart_3019394 baseEnd_3019394 := by
    simpa [prefixWord, tailWord_3019394, baseEnd_3019394] using wordTrace_append hprefix tailTrace_3019394
  have hstable : (prefixWord ++ tailWord_3019394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019394).length < 2 ^ (prefixWord ++ tailWord_3019394).sum := by decide
  have hdescent : baseEnd_3019394 < baseStart_3019394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019399 : List Nat := [1, 1, 4, 2, 1, 2, 4, 7]
def baseStart_3019399 : Nat := 118140960795 + 3019399 * 2 ^ 59
def prefixEnd_3019399 : Nat := 4983230072969 + 3 ^ 40 * 3019399 * 2
def baseEnd_3019399 : Nat := 114844664792958320090855

theorem tailTrace_3019399 : CollatzResearch.WordTrace tailWord_3019399 prefixEnd_3019399 114844664792958320090855 := by
  unfold tailWord_3019399
  simp only [CollatzResearch.WordTrace]
  refine ⟨110126528788240570139541251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73417685858827046759694167 110126528788240570139541251)
  ·
    refine ⟨165189793182360855209311877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110126528788240570139541251 165189793182360855209311877)
    ·
      refine ⟨30973086221692660351745977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165189793182360855209311877 30973086221692660351745977)
      ·
        refine ⟨23229814666269495263809483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30973086221692660351745977 23229814666269495263809483)
        ·
          refine ⟨34844721999404242895714225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23229814666269495263809483 34844721999404242895714225)
          ·
            refine ⟨26133541499553182171785669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34844721999404242895714225 26133541499553182171785669)
            ·
              refine ⟨4900039031166221657209813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26133541499553182171785669 4900039031166221657209813)
              ·
                refine ⟨114844664792958320090855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4900039031166221657209813 114844664792958320090855)
                ·
                  rfl

theorem cell22_3019399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 7].length) (baseStart_3019399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019399 prefixEnd_3019399 := by exact prefixLift 3019399
  have htrace : WordTrace (prefixWord ++ tailWord_3019399) baseStart_3019399 baseEnd_3019399 := by
    simpa [prefixWord, tailWord_3019399, baseEnd_3019399] using wordTrace_append hprefix tailTrace_3019399
  have hstable : (prefixWord ++ tailWord_3019399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019399).length < 2 ^ (prefixWord ++ tailWord_3019399).sum := by decide
  have hdescent : baseEnd_3019399 < baseStart_3019399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019506 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_3019506 : Nat := 118140960795 + 3019506 * 2 ^ 59
def prefixEnd_3019506 : Nat := 4983230072969 + 3 ^ 40 * 3019506 * 2
def baseEnd_3019506 : Nat := 344546203807770756130789

theorem tailTrace_3019506 : CollatzResearch.WordTrace tailWord_3019506 prefixEnd_3019506 344546203807770756130789 := by
  unfold tailWord_3019506
  simp only [CollatzResearch.WordTrace]
  refine ⟨27532607849713231853421593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73420287599235284942457581 27532607849713231853421593)
  ·
    refine ⟨20649455887284923890066195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27532607849713231853421593 20649455887284923890066195)
    ·
      refine ⟨30974183830927385835099293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20649455887284923890066195 30974183830927385835099293)
      ·
        refine ⟨11615318936597769688162235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30974183830927385835099293 11615318936597769688162235)
        ·
          refine ⟨17422978404896654532243353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11615318936597769688162235 17422978404896654532243353)
          ·
            refine ⟨13067233803672490899182515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17422978404896654532243353 13067233803672490899182515)
            ·
              refine ⟨19600850705508736348773773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13067233803672490899182515 19600850705508736348773773)
              ·
                refine ⟨7350319014565776130790165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19600850705508736348773773 7350319014565776130790165)
                ·
                  refine ⟨344546203807770756130789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7350319014565776130790165 344546203807770756130789)
                  ·
                    rfl

theorem cell22_3019506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_3019506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019506 prefixEnd_3019506 := by exact prefixLift 3019506
  have htrace : WordTrace (prefixWord ++ tailWord_3019506) baseStart_3019506 baseEnd_3019506 := by
    simpa [prefixWord, tailWord_3019506, baseEnd_3019506] using wordTrace_append hprefix tailTrace_3019506
  have hstable : (prefixWord ++ tailWord_3019506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019506).length < 2 ^ (prefixWord ++ tailWord_3019506).sum := by decide
  have hdescent : baseEnd_3019506 < baseStart_3019506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019551 : List Nat := [1, 1, 2, 4, 2, 4, 8]
def baseStart_3019551 : Nat := 118140960795 + 3019551 * 2 ^ 59
def prefixEnd_3019551 : Nat := 4983230072969 + 3 ^ 40 * 3019551 * 2
def baseEnd_3019551 : Nat := 38283482068257301889527

theorem tailTrace_3019551 : CollatzResearch.WordTrace tailWord_3019551 prefixEnd_3019551 38283482068257301889527 := by
  unfold tailWord_3019551
  simp only [CollatzResearch.WordTrace]
  refine ⟨110132072683689900099074507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73421381789126600066049671 110132072683689900099074507)
  ·
    refine ⟨165198109025534850148611761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110132072683689900099074507 165198109025534850148611761)
    ·
      refine ⟨123898581769151137611458821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165198109025534850148611761 123898581769151137611458821)
      ·
        refine ⟨23230984081715838302148529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123898581769151137611458821 23230984081715838302148529)
        ·
          refine ⟨17423238061286878726611397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23230984081715838302148529 17423238061286878726611397)
          ·
            refine ⟨3266857136491289761239637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17423238061286878726611397 3266857136491289761239637)
            ·
              refine ⟨38283482068257301889527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3266857136491289761239637 38283482068257301889527)
              ·
                rfl

theorem cell22_3019551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 8].length) (baseStart_3019551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019551 prefixEnd_3019551 := by exact prefixLift 3019551
  have htrace : WordTrace (prefixWord ++ tailWord_3019551) baseStart_3019551 baseEnd_3019551 := by
    simpa [prefixWord, tailWord_3019551, baseEnd_3019551] using wordTrace_append hprefix tailTrace_3019551
  have hstable : (prefixWord ++ tailWord_3019551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019551).length < 2 ^ (prefixWord ++ tailWord_3019551).sum := by decide
  have hdescent : baseEnd_3019551 < baseStart_3019551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019572 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3019572 : Nat := 118140960795 + 3019572 * 2 ^ 59
def prefixEnd_3019572 : Nat := 4983230072969 + 3 ^ 40 * 3019572 * 2
def baseEnd_3019572 : Nat := 1033661204572110096242165

theorem tailTrace_3019572 : CollatzResearch.WordTrace tailWord_3019572 prefixEnd_3019572 1033661204572110096242165 := by
  unfold tailWord_3019572
  simp only [CollatzResearch.WordTrace]
  refine ⟨55066419308306910342794485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73421892411075880457059313 55066419308306910342794485)
  ·
    refine ⟨5162476810153772844636983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55066419308306910342794485 5162476810153772844636983)
    ·
      refine ⟨7743715215230659266955475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5162476810153772844636983 7743715215230659266955475)
      ·
        refine ⟨11615572822845988900433213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7743715215230659266955475 11615572822845988900433213)
        ·
          refine ⟨4355839808567245837662455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11615572822845988900433213 4355839808567245837662455)
          ·
            refine ⟨6533759712850868756493683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355839808567245837662455 6533759712850868756493683)
            ·
              refine ⟨9800639569276303134740525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533759712850868756493683 9800639569276303134740525)
              ·
                refine ⟨3675239838478613675527697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9800639569276303134740525 3675239838478613675527697)
                ·
                  refine ⟨2756429878858960256645773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3675239838478613675527697 2756429878858960256645773)
                  ·
                    refine ⟨1033661204572110096242165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2756429878858960256645773 1033661204572110096242165)
                    ·
                      rfl

theorem cell22_3019572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3019572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019572 prefixEnd_3019572 := by exact prefixLift 3019572
  have htrace : WordTrace (prefixWord ++ tailWord_3019572) baseStart_3019572 baseEnd_3019572 := by
    simpa [prefixWord, tailWord_3019572, baseEnd_3019572] using wordTrace_append hprefix tailTrace_3019572
  have hstable : (prefixWord ++ tailWord_3019572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019572).length < 2 ^ (prefixWord ++ tailWord_3019572).sum := by decide
  have hdescent : baseEnd_3019572 < baseStart_3019572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019641 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 8]
def baseStart_3019641 : Nat := 118140960795 + 3019641 * 2 ^ 59
def prefixEnd_3019641 : Nat := 4983230072969 + 3 ^ 40 * 3019641 * 2
def baseEnd_3019641 : Nat := 344561608227405638755651

theorem tailTrace_3019641 : CollatzResearch.WordTrace tailWord_3019641 prefixEnd_3019641 344561608227405638755651 := by
  unfold tailWord_3019641
  simp only [CollatzResearch.WordTrace]
  refine ⟨110135355253363845469850777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73423570168909230313233851 110135355253363845469850777)
  ·
    refine ⟨82601516440022884102388083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110135355253363845469850777 82601516440022884102388083)
    ·
      refine ⟨123902274660034326153582125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82601516440022884102388083 123902274660034326153582125)
      ·
        refine ⟨46463352997512872307593297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123902274660034326153582125 46463352997512872307593297)
        ·
          refine ⟨34847514748134654230694973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46463352997512872307593297 34847514748134654230694973)
          ·
            refine ⟨13067818030550495336510615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34847514748134654230694973 13067818030550495336510615)
            ·
              refine ⟨19601727045825743004765923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13067818030550495336510615 19601727045825743004765923)
              ·
                refine ⟨29402590568738614507148885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19601727045825743004765923 29402590568738614507148885)
                ·
                  refine ⟨344561608227405638755651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29402590568738614507148885 344561608227405638755651)
                  ·
                    rfl

theorem cell22_3019641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_3019641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019641 prefixEnd_3019641 := by exact prefixLift 3019641
  have htrace : WordTrace (prefixWord ++ tailWord_3019641) baseStart_3019641 baseEnd_3019641 := by
    simpa [prefixWord, tailWord_3019641, baseEnd_3019641] using wordTrace_append hprefix tailTrace_3019641
  have hstable : (prefixWord ++ tailWord_3019641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019641).length < 2 ^ (prefixWord ++ tailWord_3019641).sum := by decide
  have hdescent : baseEnd_3019641 < baseStart_3019641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019660 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_3019660 : Nat := 118140960795 + 3019660 * 2 ^ 59
def prefixEnd_3019660 : Nat := 4983230072969 + 3 ^ 40 * 3019660 * 2
def baseEnd_3019660 : Nat := 1033691328770507200041895

theorem tailTrace_3019660 : CollatzResearch.WordTrace tailWord_3019660 prefixEnd_3019660 1033691328770507200041895 := by
  unfold tailWord_3019660
  simp only [CollatzResearch.WordTrace]
  refine ⟨55068024120147505857396217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73424032160196674476528289 55068024120147505857396217)
  ·
    refine ⟨41301018090110629393047163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55068024120147505857396217 41301018090110629393047163)
    ·
      refine ⟨61951527135165944089570745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41301018090110629393047163 61951527135165944089570745)
      ·
        refine ⟨46463645351374458067178059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61951527135165944089570745 46463645351374458067178059)
        ·
          refine ⟨69695468027061687100767089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46463645351374458067178059 69695468027061687100767089)
          ·
            refine ⟨52271601020296265325575317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69695468027061687100767089 52271601020296265325575317)
            ·
              refine ⟨2450231297826387437136343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52271601020296265325575317 2450231297826387437136343)
              ·
                refine ⟨3675346946739581155704515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450231297826387437136343 3675346946739581155704515)
                ·
                  refine ⟨5513020420109371733556773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675346946739581155704515 5513020420109371733556773)
                  ·
                    refine ⟨1033691328770507200041895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5513020420109371733556773 1033691328770507200041895)
                    ·
                      rfl

theorem cell22_3019660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_3019660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019660 prefixEnd_3019660 := by exact prefixLift 3019660
  have htrace : WordTrace (prefixWord ++ tailWord_3019660) baseStart_3019660 baseEnd_3019660 := by
    simpa [prefixWord, tailWord_3019660, baseEnd_3019660] using wordTrace_append hprefix tailTrace_3019660
  have hstable : (prefixWord ++ tailWord_3019660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019660).length < 2 ^ (prefixWord ++ tailWord_3019660).sum := by decide
  have hdescent : baseEnd_3019660 < baseStart_3019660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019703 : List Nat := [1, 1, 3, 1, 3, 1, 6, 6]
def baseStart_3019703 : Nat := 118140960795 + 3019703 * 2 ^ 59
def prefixEnd_3019703 : Nat := 4983230072969 + 3 ^ 40 * 3019703 * 2
def baseEnd_3019703 : Nat := 114856227616585491246307

theorem tailTrace_3019703 : CollatzResearch.WordTrace tailWord_3019703 prefixEnd_3019703 114856227616585491246307 := by
  unfold tailWord_3019703
  simp only [CollatzResearch.WordTrace]
  refine ⟨110137616579139230058607763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73425077719426153372405175 110137616579139230058607763)
  ·
    refine ⟨165206424868708845087911645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110137616579139230058607763 165206424868708845087911645)
    ·
      refine ⟨61952409325765816907966867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165206424868708845087911645 61952409325765816907966867)
      ·
        refine ⟨92928613988648725361950301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61952409325765816907966867 92928613988648725361950301)
        ·
          refine ⟨34848230245743272010731363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92928613988648725361950301 34848230245743272010731363)
          ·
            refine ⟨52272345368614908016097045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34848230245743272010731363 52272345368614908016097045)
            ·
              refine ⟨2450266189153823813254549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52272345368614908016097045 2450266189153823813254549)
              ·
                refine ⟨114856227616585491246307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2450266189153823813254549 114856227616585491246307)
                ·
                  rfl

theorem cell22_3019703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 6].length) (baseStart_3019703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019703 prefixEnd_3019703 := by exact prefixLift 3019703
  have htrace : WordTrace (prefixWord ++ tailWord_3019703) baseStart_3019703 baseEnd_3019703 := by
    simpa [prefixWord, tailWord_3019703, baseEnd_3019703] using wordTrace_append hprefix tailTrace_3019703
  have hstable : (prefixWord ++ tailWord_3019703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019703).length < 2 ^ (prefixWord ++ tailWord_3019703).sum := by decide
  have hdescent : baseEnd_3019703 < baseStart_3019703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019709 : List Nat := [1, 4, 1, 2, 5, 1, 1, 3, 4]
def baseStart_3019709 : Nat := 118140960795 + 3019709 * 2 ^ 59
def prefixEnd_3019709 : Nat := 4983230072969 + 3 ^ 40 * 3019709 * 2
def baseEnd_3019709 : Nat := 344569367490629135188915

theorem tailTrace_3019709 : CollatzResearch.WordTrace tailWord_3019709 prefixEnd_3019709 344569367490629135188915 := by
  unfold tailWord_3019709
  simp only [CollatzResearch.WordTrace]
  refine ⟨110137835417117493083326181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73425223611411662055550787 110137835417117493083326181)
  ·
    refine ⟨20650844140709529953123659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110137835417117493083326181 20650844140709529953123659)
    ·
      refine ⟨30976266211064294929685489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20650844140709529953123659 30976266211064294929685489)
      ·
        refine ⟨23232199658298221197264117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30976266211064294929685489 23232199658298221197264117)
        ·
          refine ⟨2178018717965458237243511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23232199658298221197264117 2178018717965458237243511)
          ·
            refine ⟨3267028076948187355865267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178018717965458237243511 3267028076948187355865267)
            ·
              refine ⟨4900542115422281033797901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267028076948187355865267 4900542115422281033797901)
              ·
                refine ⟨1837703293283355387674213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4900542115422281033797901 1837703293283355387674213)
                ·
                  refine ⟨344569367490629135188915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837703293283355387674213 344569367490629135188915)
                  ·
                    rfl

theorem cell22_3019709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_3019709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019709 prefixEnd_3019709 := by exact prefixLift 3019709
  have htrace : WordTrace (prefixWord ++ tailWord_3019709) baseStart_3019709 baseEnd_3019709 := by
    simpa [prefixWord, tailWord_3019709, baseEnd_3019709] using wordTrace_append hprefix tailTrace_3019709
  have hstable : (prefixWord ++ tailWord_3019709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019709).length < 2 ^ (prefixWord ++ tailWord_3019709).sum := by decide
  have hdescent : baseEnd_3019709 < baseStart_3019709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019720 : List Nat := [2, 1, 3, 1, 6, 1, 8]
def baseStart_3019720 : Nat := 118140960795 + 3019720 * 2 ^ 59
def prefixEnd_3019720 : Nat := 4983230072969 + 3 ^ 40 * 3019720 * 2
def baseEnd_3019720 : Nat := 38285624740618038649693

theorem tailTrace_3019720 : CollatzResearch.WordTrace tailWord_3019720 prefixEnd_3019720 38285624740618038649693 := by
  unfold tailWord_3019720
  simp only [CollatzResearch.WordTrace]
  refine ⟨55069118310038820980988307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73425491080051761307984409 55069118310038820980988307)
  ·
    refine ⟨82603677465058231471482461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55069118310038820980988307 82603677465058231471482461)
    ·
      refine ⟨30976379049396836801805923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82603677465058231471482461 30976379049396836801805923)
      ·
        refine ⟨46464568574095255202708885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30976379049396836801805923 46464568574095255202708885)
        ·
          refine ⟨2178026651910715087626979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46464568574095255202708885 2178026651910715087626979)
          ·
            refine ⟨3267039977866072631440469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178026651910715087626979 3267039977866072631440469)
            ·
              refine ⟨38285624740618038649693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3267039977866072631440469 38285624740618038649693)
              ·
                rfl

theorem cell22_3019720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 8].length) (baseStart_3019720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019720 prefixEnd_3019720 := by exact prefixLift 3019720
  have htrace : WordTrace (prefixWord ++ tailWord_3019720) baseStart_3019720 baseEnd_3019720 := by
    simpa [prefixWord, tailWord_3019720, baseEnd_3019720] using wordTrace_append hprefix tailTrace_3019720
  have hstable : (prefixWord ++ tailWord_3019720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019720).length < 2 ^ (prefixWord ++ tailWord_3019720).sum := by decide
  have hdescent : baseEnd_3019720 < baseStart_3019720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019786 : List Nat := [3, 1, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_3019786 : Nat := 118140960795 + 3019786 * 2 ^ 59
def prefixEnd_3019786 : Nat := 4983230072969 + 3 ^ 40 * 3019786 * 2
def baseEnd_3019786 : Nat := 1033734461145484871391509

theorem tailTrace_3019786 : CollatzResearch.WordTrace tailWord_3019786 prefixEnd_3019786 1033734461145484871391509 := by
  unfold tailWord_3019786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27535160959459633808469803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73427095891892356822586141 27535160959459633808469803)
  ·
    refine ⟨41302741439189450712704705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27535160959459633808469803 41302741439189450712704705)
    ·
      refine ⟨30977056079392088034528529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41302741439189450712704705 30977056079392088034528529)
      ·
        refine ⟨23232792059544066025896397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30977056079392088034528529 23232792059544066025896397)
        ·
          refine ⟨8712297022329024759711149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23232792059544066025896397 8712297022329024759711149)
          ·
            refine ⟨3267111383373384284891681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8712297022329024759711149 3267111383373384284891681)
            ·
              refine ⟨2450333537530038213668761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3267111383373384284891681 2450333537530038213668761)
              ·
                refine ⟨1837750153147528660251571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2450333537530038213668761 1837750153147528660251571)
                ·
                  refine ⟨2756625229721292990377357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837750153147528660251571 2756625229721292990377357)
                  ·
                    refine ⟨1033734461145484871391509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2756625229721292990377357 1033734461145484871391509)
                    ·
                      rfl

theorem cell22_3019786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_3019786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019786 prefixEnd_3019786 := by exact prefixLift 3019786
  have htrace : WordTrace (prefixWord ++ tailWord_3019786) baseStart_3019786 baseEnd_3019786 := by
    simpa [prefixWord, tailWord_3019786, baseEnd_3019786] using wordTrace_append hprefix tailTrace_3019786
  have hstable : (prefixWord ++ tailWord_3019786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019786).length < 2 ^ (prefixWord ++ tailWord_3019786).sum := by decide
  have hdescent : baseEnd_3019786 < baseStart_3019786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019810 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3019810 : Nat := 118140960795 + 3019810 * 2 ^ 59
def prefixEnd_3019810 : Nat := 4983230072969 + 3 ^ 40 * 3019810 * 2
def baseEnd_3019810 : Nat := 344580892278652269597145

theorem tailTrace_3019810 : CollatzResearch.WordTrace tailWord_3019810 prefixEnd_3019810 344580892278652269597145 := by
  unfold tailWord_3019810
  simp only [CollatzResearch.WordTrace]
  refine ⟨27535379797437896833188221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73427679459834391555168589 27535379797437896833188221)
  ·
    refine ⟨10325767424039211312445583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27535379797437896833188221 10325767424039211312445583)
    ·
      refine ⟨15488651136058816968668375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10325767424039211312445583 15488651136058816968668375)
      ·
        refine ⟨23232976704088225453002563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15488651136058816968668375 23232976704088225453002563)
        ·
          refine ⟨34849465056132338179503845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23232976704088225453002563 34849465056132338179503845)
          ·
            refine ⟨6534274698024813408656971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34849465056132338179503845 6534274698024813408656971)
            ·
              refine ⟨9801412047037220112985457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6534274698024813408656971 9801412047037220112985457)
              ·
                refine ⟨7351059035277915084739093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9801412047037220112985457 7351059035277915084739093)
                ·
                  refine ⟨344580892278652269597145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7351059035277915084739093 344580892278652269597145)
                  ·
                    rfl

theorem cell22_3019810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3019810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019810 prefixEnd_3019810 := by exact prefixLift 3019810
  have htrace : WordTrace (prefixWord ++ tailWord_3019810) baseStart_3019810 baseEnd_3019810 := by
    simpa [prefixWord, tailWord_3019810, baseEnd_3019810] using wordTrace_append hprefix tailTrace_3019810
  have hstable : (prefixWord ++ tailWord_3019810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019810).length < 2 ^ (prefixWord ++ tailWord_3019810).sum := by decide
  have hdescent : baseEnd_3019810 < baseStart_3019810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019825 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 4, 3]
def baseStart_3019825 : Nat := 118140960795 + 3019825 * 2 ^ 59
def prefixEnd_3019825 : Nat := 4983230072969 + 3 ^ 40 * 3019825 * 2
def baseEnd_3019825 : Nat := 1033747811642501769666389

theorem tailTrace_3019825 : CollatzResearch.WordTrace tailWord_3019825 prefixEnd_3019825 1033747811642501769666389 := by
  unfold tailWord_3019825
  simp only [CollatzResearch.WordTrace]
  refine ⟨110142066284697244894548929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73428044189798163263032619 110142066284697244894548929)
  ·
    refine ⟨82606549713522933670911697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110142066284697244894548929 82606549713522933670911697)
    ·
      refine ⟨61954912285142200253183773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82606549713522933670911697 61954912285142200253183773)
      ·
        refine ⟨23233092106928325094943915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61954912285142200253183773 23233092106928325094943915)
        ·
          refine ⟨34849638160392487642415873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23233092106928325094943915 34849638160392487642415873)
          ·
            refine ⟨26137228620294365731811905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34849638160392487642415873 26137228620294365731811905)
            ·
              refine ⟨19602921465220774298858929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26137228620294365731811905 19602921465220774298858929)
              ·
                refine ⟨14702191098915580724144197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19602921465220774298858929 14702191098915580724144197)
                ·
                  refine ⟨2756660831046671385777037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14702191098915580724144197 2756660831046671385777037)
                  ·
                    refine ⟨1033747811642501769666389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2756660831046671385777037 1033747811642501769666389)
                    ·
                      rfl

theorem cell22_3019825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_3019825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019825 prefixEnd_3019825 := by exact prefixLift 3019825
  have htrace : WordTrace (prefixWord ++ tailWord_3019825) baseStart_3019825 baseEnd_3019825 := by
    simpa [prefixWord, tailWord_3019825, baseEnd_3019825] using wordTrace_append hprefix tailTrace_3019825
  have hstable : (prefixWord ++ tailWord_3019825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019825).length < 2 ^ (prefixWord ++ tailWord_3019825).sum := by decide
  have hdescent : baseEnd_3019825 < baseStart_3019825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019900 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 5]
def baseStart_3019900 : Nat := 118140960795 + 3019900 * 2 ^ 59
def prefixEnd_3019900 : Nat := 4983230072969 + 3 ^ 40 * 3019900 * 2
def baseEnd_3019900 : Nat := 344591161891742191347053

theorem tailTrace_3019900 : CollatzResearch.WordTrace tailWord_3019900 prefixEnd_3019900 344591161891742191347053 := by
  unfold tailWord_3019900
  simp only [CollatzResearch.WordTrace]
  refine ⟨55072400879712766351764577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73429867839617021802352769 55072400879712766351764577)
  ·
    refine ⟨41304300659784574763823433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55072400879712766351764577 41304300659784574763823433)
    ·
      refine ⟨30978225494838431072867575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41304300659784574763823433 30978225494838431072867575)
      ·
        refine ⟨46467338242257646609301363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30978225494838431072867575 46467338242257646609301363)
        ·
          refine ⟨69701007363386469913952045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46467338242257646609301363 69701007363386469913952045)
          ·
            refine ⟨26137877761269926217732017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69701007363386469913952045 26137877761269926217732017)
            ·
              refine ⟨19603408320952444663299013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26137877761269926217732017 19603408320952444663299013)
              ·
                refine ⟨3675639060178583374368565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19603408320952444663299013 3675639060178583374368565)
                ·
                  refine ⟨344591161891742191347053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3675639060178583374368565 344591161891742191347053)
                  ·
                    rfl

theorem cell22_3019900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_3019900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019900 prefixEnd_3019900 := by exact prefixLift 3019900
  have htrace : WordTrace (prefixWord ++ tailWord_3019900) baseStart_3019900 baseEnd_3019900 := by
    simpa [prefixWord, tailWord_3019900, baseEnd_3019900] using wordTrace_append hprefix tailTrace_3019900
  have hstable : (prefixWord ++ tailWord_3019900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019900).length < 2 ^ (prefixWord ++ tailWord_3019900).sum := by decide
  have hdescent : baseEnd_3019900 < baseStart_3019900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019975 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3019975 : Nat := 118140960795 + 3019975 * 2 ^ 59
def prefixEnd_3019975 : Nat := 4983230072969 + 3 ^ 40 * 3019975 * 2
def baseEnd_3019975 : Nat := 1033799159707951378415929

theorem tailTrace_3019975 : CollatzResearch.WordTrace tailWord_3019975 prefixEnd_3019975 1033799159707951378415929 := by
  unfold tailWord_3019975
  simp only [CollatzResearch.WordTrace]
  refine ⟨110147537234153820512509379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73431691489435880341672919 110147537234153820512509379)
  ·
    refine ⟨165221305851230730768764069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110147537234153820512509379 165221305851230730768764069)
    ·
      refine ⟨30978994847105762019143263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165221305851230730768764069 30978994847105762019143263)
      ·
        refine ⟨46468492270658643028714895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30978994847105762019143263 46468492270658643028714895)
        ·
          refine ⟨69702738405987964543072343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46468492270658643028714895 69702738405987964543072343)
          ·
            refine ⟨104554107608981946814608515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69702738405987964543072343 104554107608981946814608515)
            ·
              refine ⟨156831161413472920221912773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104554107608981946814608515 156831161413472920221912773)
              ·
                refine ⟨29405842765026172541608645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156831161413472920221912773 29405842765026172541608645)
                ·
                  refine ⟨5513595518442407351551621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29405842765026172541608645 5513595518442407351551621)
                  ·
                    refine ⟨1033799159707951378415929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5513595518442407351551621 1033799159707951378415929)
                    ·
                      rfl

theorem cell22_3019975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3019975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019975 prefixEnd_3019975 := by exact prefixLift 3019975
  have htrace : WordTrace (prefixWord ++ tailWord_3019975) baseStart_3019975 baseEnd_3019975 := by
    simpa [prefixWord, tailWord_3019975, baseEnd_3019975] using wordTrace_append hprefix tailTrace_3019975
  have hstable : (prefixWord ++ tailWord_3019975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019975).length < 2 ^ (prefixWord ++ tailWord_3019975).sum := by decide
  have hdescent : baseEnd_3019975 < baseStart_3019975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019992 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_3019992 : Nat := 118140960795 + 3019992 * 2 ^ 59
def prefixEnd_3019992 : Nat := 4983230072969 + 3 ^ 40 * 3019992 * 2
def baseEnd_3019992 : Nat := 1033804979155369000740877

theorem tailTrace_3019992 : CollatzResearch.WordTrace tailWord_3019992 prefixEnd_3019992 1033804979155369000740877 := by
  unfold tailWord_3019992
  simp only [CollatzResearch.WordTrace]
  refine ⟨55074078637546116207939115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73432104850061488277252153 55074078637546116207939115)
  ·
    refine ⟨82611117956319174311908673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55074078637546116207939115 82611117956319174311908673)
    ·
      refine ⟨61958338467239380733931505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82611117956319174311908673 61958338467239380733931505)
      ·
        refine ⟨46468753850429535550448629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61958338467239380733931505 46468753850429535550448629)
        ·
          refine ⟨4356445673477768957854559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46468753850429535550448629 4356445673477768957854559)
          ·
            refine ⟨6534668510216653436781839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356445673477768957854559 6534668510216653436781839)
            ·
              refine ⟨9802002765324980155172759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6534668510216653436781839 9802002765324980155172759)
              ·
                refine ⟨14703004147987470232759139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9802002765324980155172759 14703004147987470232759139)
                ·
                  refine ⟨22054506221981205349138709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14703004147987470232759139 22054506221981205349138709)
                  ·
                    refine ⟨1033804979155369000740877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22054506221981205349138709 1033804979155369000740877)
                    ·
                      rfl

theorem cell22_3019992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_3019992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3019992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3019992 prefixEnd_3019992 := by exact prefixLift 3019992
  have htrace : WordTrace (prefixWord ++ tailWord_3019992) baseStart_3019992 baseEnd_3019992 := by
    simpa [prefixWord, tailWord_3019992, baseEnd_3019992] using wordTrace_append hprefix tailTrace_3019992
  have hstable : (prefixWord ++ tailWord_3019992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019992).length < 2 ^ (prefixWord ++ tailWord_3019992).sum := by decide
  have hdescent : baseEnd_3019992 < baseStart_3019992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020007 : List Nat := [1, 1, 5, 3, 2, 1, 9]
def baseStart_3020007 : Nat := 118140960795 + 3020007 * 2 ^ 59
def prefixEnd_3020007 : Nat := 4983230072969 + 3 ^ 40 * 3020007 * 2
def baseEnd_3020007 : Nat := 38289263480070887467253

theorem tailTrace_3020007 : CollatzResearch.WordTrace tailWord_3020007 prefixEnd_3020007 38289263480070887467253 := by
  unfold tailWord_3020007
  simp only [CollatzResearch.WordTrace]
  refine ⟨110148704370037889977674275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73432469580025259985116183 110148704370037889977674275)
  ·
    refine ⟨165223056555056834966511413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110148704370037889977674275 165223056555056834966511413)
    ·
      refine ⟨15489661552036578278110445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165223056555056834966511413 15489661552036578278110445)
      ·
        refine ⟨5808623082013716854291417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15489661552036578278110445 5808623082013716854291417)
        ·
          refine ⟨4356467311510287640718563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5808623082013716854291417 4356467311510287640718563)
          ·
            refine ⟨6534700967265431461077845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356467311510287640718563 6534700967265431461077845)
            ·
              refine ⟨38289263480070887467253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6534700967265431461077845 38289263480070887467253)
              ·
                rfl

theorem cell22_3020007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 9].length) (baseStart_3020007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020007 prefixEnd_3020007 := by exact prefixLift 3020007
  have htrace : WordTrace (prefixWord ++ tailWord_3020007) baseStart_3020007 baseEnd_3020007 := by
    simpa [prefixWord, tailWord_3020007, baseEnd_3020007] using wordTrace_append hprefix tailTrace_3020007
  have hstable : (prefixWord ++ tailWord_3020007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020007).length < 2 ^ (prefixWord ++ tailWord_3020007).sum := by decide
  have hdescent : baseEnd_3020007 < baseStart_3020007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020056 : List Nat := [2, 1, 2, 3, 1, 3, 3, 3, 1, 3]
def baseStart_3020056 : Nat := 118140960795 + 3020056 * 2 ^ 59
def prefixEnd_3020056 : Nat := 4983230072969 + 3 ^ 40 * 3020056 * 2
def baseEnd_3020056 : Nat := 1033826887663294167140681

theorem tailTrace_3020056 : CollatzResearch.WordTrace tailWord_3020056 prefixEnd_3020056 1033826887663294167140681 := by
  unfold tailWord_3020056
  simp only [CollatzResearch.WordTrace]
  refine ⟨55075245773430185673104011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73433661031240247564138681 55075245773430185673104011)
  ·
    refine ⟨82612868660145278509656017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55075245773430185673104011 82612868660145278509656017)
    ·
      refine ⟨61959651495108958882242013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82612868660145278509656017 61959651495108958882242013)
      ·
        refine ⟨23234869310665859580840755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61959651495108958882242013 23234869310665859580840755)
        ·
          refine ⟨34852303965998789371261133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23234869310665859580840755 34852303965998789371261133)
          ·
            refine ⟨13069613987249546014222925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34852303965998789371261133 13069613987249546014222925)
            ·
              refine ⟨4901105245218579755333597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13069613987249546014222925 4901105245218579755333597)
              ·
                refine ⟨1837914466956967408250099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4901105245218579755333597 1837914466956967408250099)
                ·
                  refine ⟨2756871700435451112375149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837914466956967408250099 2756871700435451112375149)
                  ·
                    refine ⟨1033826887663294167140681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2756871700435451112375149 1033826887663294167140681)
                    ·
                      rfl

theorem cell22_3020056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_3020056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020056 prefixEnd_3020056 := by exact prefixLift 3020056
  have htrace : WordTrace (prefixWord ++ tailWord_3020056) baseStart_3020056 baseEnd_3020056 := by
    simpa [prefixWord, tailWord_3020056, baseEnd_3020056] using wordTrace_append hprefix tailTrace_3020056
  have hstable : (prefixWord ++ tailWord_3020056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020056).length < 2 ^ (prefixWord ++ tailWord_3020056).sum := by decide
  have hdescent : baseEnd_3020056 < baseStart_3020056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020112 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_3020112 : Nat := 118140960795 + 3020112 * 2 ^ 59
def prefixEnd_3020112 : Nat := 4983230072969 + 3 ^ 40 * 3020112 * 2
def baseEnd_3020112 : Nat := 1033846057607728687740509

theorem tailTrace_3020112 : CollatzResearch.WordTrace tailWord_3020112 prefixEnd_3020112 1033846057607728687740509 := by
  unfold tailWord_3020112
  simp only [CollatzResearch.WordTrace]
  refine ⟨55076267017328746455123295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73435022689771661940164393 55076267017328746455123295)
  ·
    refine ⟨82614400525993119682684943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55076267017328746455123295 82614400525993119682684943)
    ·
      refine ⟨123921600788989679524027415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82614400525993119682684943 123921600788989679524027415)
      ·
        refine ⟨185882401183484519286041123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123921600788989679524027415 185882401183484519286041123)
        ·
          refine ⟨278823601775226778929061685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185882401183484519286041123 278823601775226778929061685)
          ·
            refine ⟨26139712666427510524599533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278823601775226778929061685 26139712666427510524599533)
            ·
              refine ⟨9802392249910316446724825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26139712666427510524599533 9802392249910316446724825)
              ·
                refine ⟨7351794187432737335043619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9802392249910316446724825 7351794187432737335043619)
                ·
                  refine ⟨11027691281149106002565429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7351794187432737335043619 11027691281149106002565429)
                  ·
                    refine ⟨1033846057607728687740509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11027691281149106002565429 1033846057607728687740509)
                    ·
                      rfl

theorem cell22_3020112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_3020112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020112 prefixEnd_3020112 := by exact prefixLift 3020112
  have htrace : WordTrace (prefixWord ++ tailWord_3020112) baseStart_3020112 baseEnd_3020112 := by
    simpa [prefixWord, tailWord_3020112, baseEnd_3020112] using wordTrace_append hprefix tailTrace_3020112
  have hstable : (prefixWord ++ tailWord_3020112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020112).length < 2 ^ (prefixWord ++ tailWord_3020112).sum := by decide
  have hdescent : baseEnd_3020112 < baseStart_3020112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020114 : List Nat := [3, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_3020114 : Nat := 118140960795 + 3020114 * 2 ^ 59
def prefixEnd_3020114 : Nat := 4983230072969 + 3 ^ 40 * 3020114 * 2
def baseEnd_3020114 : Nat := 344615580749533783063501

theorem tailTrace_3020114 : CollatzResearch.WordTrace tailWord_3020114 prefixEnd_3020114 344615580749533783063501 := by
  unfold tailWord_3020114
  simp only [CollatzResearch.WordTrace]
  refine ⟨27538151745162561812954849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73435071320433498167879597 27538151745162561812954849)
  ·
    refine ⟨20653613808871921359716137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27538151745162561812954849 20653613808871921359716137)
    ·
      refine ⟨15490210356653941019787103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20653613808871921359716137 15490210356653941019787103)
      ·
        refine ⟨23235315534980911529680655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15490210356653941019787103 23235315534980911529680655)
        ·
          refine ⟨34852973302471367294520983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23235315534980911529680655 34852973302471367294520983)
          ·
            refine ⟨52279459953707050941781475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34852973302471367294520983 52279459953707050941781475)
            ·
              refine ⟨78419189930560576412672213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52279459953707050941781475 78419189930560576412672213)
              ·
                refine ⟨1837949763997513509672005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78419189930560576412672213 1837949763997513509672005)
                ·
                  refine ⟨344615580749533783063501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837949763997513509672005 344615580749533783063501)
                  ·
                    rfl

theorem cell22_3020114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_3020114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020114 prefixEnd_3020114 := by exact prefixLift 3020114
  have htrace : WordTrace (prefixWord ++ tailWord_3020114) baseStart_3020114 baseEnd_3020114 := by
    simpa [prefixWord, tailWord_3020114, baseEnd_3020114] using wordTrace_append hprefix tailTrace_3020114
  have hstable : (prefixWord ++ tailWord_3020114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020114).length < 2 ^ (prefixWord ++ tailWord_3020114).sum := by decide
  have hdescent : baseEnd_3020114 < baseStart_3020114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020116 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3020116 : Nat := 118140960795 + 3020116 * 2 ^ 59
def prefixEnd_3020116 : Nat := 4983230072969 + 3 ^ 40 * 3020116 * 2
def baseEnd_3020116 : Nat := 1033847426889474010640497

theorem tailTrace_3020116 : CollatzResearch.WordTrace tailWord_3020116 prefixEnd_3020116 1033847426889474010640497 := by
  unfold tailWord_3020116
  simp only [CollatzResearch.WordTrace]
  refine ⟨55076339963321500796696101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73435119951095334395594801 55076339963321500796696101)
  ·
    refine ⟨10326813743122781399380519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55076339963321500796696101 10326813743122781399380519)
    ·
      refine ⟨15490220614684172099070779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10326813743122781399380519 15490220614684172099070779)
      ·
        refine ⟨23235330922026258148606169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15490220614684172099070779 23235330922026258148606169)
        ·
          refine ⟨17426498191519693611454627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23235330922026258148606169 17426498191519693611454627)
          ·
            refine ⟨26139747287279540417181941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17426498191519693611454627 26139747287279540417181941)
            ·
              refine ⟨2450601308182456914110807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26139747287279540417181941 2450601308182456914110807)
              ·
                refine ⟨3675901962273685371166211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450601308182456914110807 3675901962273685371166211)
                ·
                  refine ⟨5513852943410528056749317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675901962273685371166211 5513852943410528056749317)
                  ·
                    refine ⟨1033847426889474010640497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5513852943410528056749317 1033847426889474010640497)
                    ·
                      rfl

theorem cell22_3020116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3020116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020116 prefixEnd_3020116 := by exact prefixLift 3020116
  have htrace : WordTrace (prefixWord ++ tailWord_3020116) baseStart_3020116 baseEnd_3020116 := by
    simpa [prefixWord, tailWord_3020116, baseEnd_3020116] using wordTrace_append hprefix tailTrace_3020116
  have hstable : (prefixWord ++ tailWord_3020116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020116).length < 2 ^ (prefixWord ++ tailWord_3020116).sum := by decide
  have hdescent : baseEnd_3020116 < baseStart_3020116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020131 : List Nat := [1, 1, 1, 5, 2, 2, 4, 2, 4]
def baseStart_3020131 : Nat := 118140960795 + 3020131 * 2 ^ 59
def prefixEnd_3020131 : Nat := 4983230072969 + 3 ^ 40 * 3020131 * 2
def baseEnd_3020131 : Nat := 344617520565339657171817

theorem tailTrace_3020131 : CollatzResearch.WordTrace tailWord_3020131 prefixEnd_3020131 344617520565339657171817 := by
  unfold tailWord_3020131
  simp only [CollatzResearch.WordTrace]
  refine ⟨110153227021588659155188247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73435484681059106103458831 110153227021588659155188247)
  ·
    refine ⟨165229840532382988732782371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110153227021588659155188247 165229840532382988732782371)
    ·
      refine ⟨247844760798574483099173557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165229840532382988732782371 247844760798574483099173557)
      ·
        refine ⟨23235446324866357790547521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247844760798574483099173557 23235446324866357790547521)
        ·
          refine ⟨17426584743649768342910641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23235446324866357790547521 17426584743649768342910641)
          ·
            refine ⟨13069938557737326257182981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17426584743649768342910641 13069938557737326257182981)
            ·
              refine ⟨2450613479575748673221809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13069938557737326257182981 2450613479575748673221809)
              ·
                refine ⟨1837960109681811504916357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2450613479575748673221809 1837960109681811504916357)
                ·
                  refine ⟨344617520565339657171817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837960109681811504916357 344617520565339657171817)
                  ·
                    rfl

theorem cell22_3020131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 4].length) (baseStart_3020131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020131 prefixEnd_3020131 := by exact prefixLift 3020131
  have htrace : WordTrace (prefixWord ++ tailWord_3020131) baseStart_3020131 baseEnd_3020131 := by
    simpa [prefixWord, tailWord_3020131, baseEnd_3020131] using wordTrace_append hprefix tailTrace_3020131
  have hstable : (prefixWord ++ tailWord_3020131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020131).length < 2 ^ (prefixWord ++ tailWord_3020131).sum := by decide
  have hdescent : baseEnd_3020131 < baseStart_3020131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020191 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 3, 3]
def baseStart_3020191 : Nat := 118140960795 + 3020191 * 2 ^ 59
def prefixEnd_3020191 : Nat := 4983230072969 + 3 ^ 40 * 3020191 * 2
def baseEnd_3020191 : Nat := 1033873100922198815015267

theorem tailTrace_3020191 : CollatzResearch.WordTrace tailWord_3020191 prefixEnd_3020191 1033873100922198815015267 := by
  unfold tailWord_3020191
  simp only [CollatzResearch.WordTrace]
  refine ⟨110155415401371289402372427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73436943600914192934914951 110155415401371289402372427)
  ·
    refine ⟨165233123102056934103558641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110155415401371289402372427 165233123102056934103558641)
    ·
      refine ⟨123924842326542700577668981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165233123102056934103558641 123924842326542700577668981)
      ·
        refine ⟨11617953968113378179156467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123924842326542700577668981 11617953968113378179156467)
        ·
          refine ⟨17426930952170067268734701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11617953968113378179156467 17426930952170067268734701)
          ·
            refine ⟨6535099107063775225775513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17426930952170067268734701 6535099107063775225775513)
            ·
              refine ⟨4901324330297831419331635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6535099107063775225775513 4901324330297831419331635)
              ·
                refine ⟨7351986495446747128997453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901324330297831419331635 7351986495446747128997453)
                ·
                  refine ⟨2756994935792530173374045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7351986495446747128997453 2756994935792530173374045)
                  ·
                    refine ⟨1033873100922198815015267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2756994935792530173374045 1033873100922198815015267)
                    ·
                      rfl

theorem cell22_3020191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_3020191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020191 prefixEnd_3020191 := by exact prefixLift 3020191
  have htrace : WordTrace (prefixWord ++ tailWord_3020191) baseStart_3020191 baseEnd_3020191 := by
    simpa [prefixWord, tailWord_3020191, baseEnd_3020191] using wordTrace_append hprefix tailTrace_3020191
  have hstable : (prefixWord ++ tailWord_3020191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020191).length < 2 ^ (prefixWord ++ tailWord_3020191).sum := by decide
  have hdescent : baseEnd_3020191 < baseStart_3020191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020249 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 6]
def baseStart_3020249 : Nat := 118140960795 + 3020249 * 2 ^ 59
def prefixEnd_3020249 : Nat := 4983230072969 + 3 ^ 40 * 3020249 * 2
def baseEnd_3020249 : Nat := 344630985169168665688363

theorem tailTrace_3020249 : CollatzResearch.WordTrace tailWord_3020249 prefixEnd_3020249 344630985169168665688363 := by
  unfold tailWord_3020249
  simp only [CollatzResearch.WordTrace]
  refine ⟨110157530835161165307983801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73438353890107443538655867 110157530835161165307983801)
  ·
    refine ⟨82618148126370873980987851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110157530835161165307983801 82618148126370873980987851)
    ·
      refine ⟨123927222189556310971481777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82618148126370873980987851 123927222189556310971481777)
      ·
        refine ⟨92945416642167233228611333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123927222189556310971481777 92945416642167233228611333)
        ·
          refine ⟨17427265620406356230364625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92945416642167233228611333 17427265620406356230364625)
          ·
            refine ⟨13070449215304767172773469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17427265620406356230364625 13070449215304767172773469)
            ·
              refine ⟨4901418455739287689790051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13070449215304767172773469 4901418455739287689790051)
              ·
                refine ⟨7352127683608931534685077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901418455739287689790051 7352127683608931534685077)
                ·
                  refine ⟨344630985169168665688363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7352127683608931534685077 344630985169168665688363)
                  ·
                    rfl

theorem cell22_3020249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_3020249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020249 prefixEnd_3020249 := by exact prefixLift 3020249
  have htrace : WordTrace (prefixWord ++ tailWord_3020249) baseStart_3020249 baseEnd_3020249 := by
    simpa [prefixWord, tailWord_3020249, baseEnd_3020249] using wordTrace_append hprefix tailTrace_3020249
  have hstable : (prefixWord ++ tailWord_3020249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020249).length < 2 ^ (prefixWord ++ tailWord_3020249).sum := by decide
  have hdescent : baseEnd_3020249 < baseStart_3020249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020264 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3020264 : Nat := 118140960795 + 3020264 * 2 ^ 59
def prefixEnd_3020264 : Nat := 4983230072969 + 3 ^ 40 * 3020264 * 2
def baseEnd_3020264 : Nat := 1033898090314050957940043

theorem tailTrace_3020264 : CollatzResearch.WordTrace tailWord_3020264 prefixEnd_3020264 1033898090314050957940043 := by
  unfold tailWord_3020264
  simp only [CollatzResearch.WordTrace]
  refine ⟨55079038965053411434889923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73438718620071215246519897 55079038965053411434889923)
  ·
    refine ⟨82618558447580117152334885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55079038965053411434889923 82618558447580117152334885)
    ·
      refine ⟨15490979708921271966062791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82618558447580117152334885 15490979708921271966062791)
      ·
        refine ⟨23236469563381907949094187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15490979708921271966062791 23236469563381907949094187)
        ·
          refine ⟨34854704345072861923641281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23236469563381907949094187 34854704345072861923641281)
          ·
            refine ⟨26141028258804646442730961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34854704345072861923641281 26141028258804646442730961)
            ·
              refine ⟨19605771194103484832048221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26141028258804646442730961 19605771194103484832048221)
              ·
                refine ⟨7352164197788806812018083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19605771194103484832048221 7352164197788806812018083)
                ·
                  refine ⟨11028246296683210218027125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7352164197788806812018083 11028246296683210218027125)
                  ·
                    refine ⟨1033898090314050957940043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11028246296683210218027125 1033898090314050957940043)
                    ·
                      rfl

theorem cell22_3020264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3020264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020264 prefixEnd_3020264 := by exact prefixLift 3020264
  have htrace : WordTrace (prefixWord ++ tailWord_3020264) baseStart_3020264 baseEnd_3020264 := by
    simpa [prefixWord, tailWord_3020264, baseEnd_3020264] using wordTrace_append hprefix tailTrace_3020264
  have hstable : (prefixWord ++ tailWord_3020264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020264).length < 2 ^ (prefixWord ++ tailWord_3020264).sum := by decide
  have hdescent : baseEnd_3020264 < baseStart_3020264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020298 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_3020298 : Nat := 118140960795 + 3020298 * 2 ^ 59
def prefixEnd_3020298 : Nat := 4983230072969 + 3 ^ 40 * 3020298 * 2
def baseEnd_3020298 : Nat := 1033909729208886202589939

theorem tailTrace_3020298 : CollatzResearch.WordTrace tailWord_3020298 prefixEnd_3020298 1033909729208886202589939 := by
  unfold tailWord_3020298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27539829502995911669129387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73439545341322431117678365 27539829502995911669129387)
  ·
    refine ⟨41309744254493867503694081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27539829502995911669129387 41309744254493867503694081)
    ·
      refine ⟨30982308190870400627770561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41309744254493867503694081 30982308190870400627770561)
      ·
        refine ⟨23236731143152800470827921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30982308190870400627770561 23236731143152800470827921)
        ·
          refine ⟨17427548357364600353120941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23236731143152800470827921 17427548357364600353120941)
          ·
            refine ⟨6535330634011725132420353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17427548357364600353120941 6535330634011725132420353)
            ·
              refine ⟨4901497975508793849315265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6535330634011725132420353 4901497975508793849315265)
              ·
                refine ⟨3676123481631595386986449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901497975508793849315265 3676123481631595386986449)
                ·
                  refine ⟨2757092611223696540239837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676123481631595386986449 2757092611223696540239837)
                  ·
                    refine ⟨1033909729208886202589939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757092611223696540239837 1033909729208886202589939)
                    ·
                      rfl

theorem cell22_3020298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_3020298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020298 prefixEnd_3020298 := by exact prefixLift 3020298
  have htrace : WordTrace (prefixWord ++ tailWord_3020298) baseStart_3020298 baseEnd_3020298 := by
    simpa [prefixWord, tailWord_3020298, baseEnd_3020298] using wordTrace_append hprefix tailTrace_3020298
  have hstable : (prefixWord ++ tailWord_3020298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020298).length < 2 ^ (prefixWord ++ tailWord_3020298).sum := by decide
  have hdescent : baseEnd_3020298 < baseStart_3020298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020300 : List Nat := [2, 2, 1, 2, 5, 2, 2, 2, 4]
def baseStart_3020300 : Nat := 118140960795 + 3020300 * 2 ^ 59
def prefixEnd_3020300 : Nat := 4983230072969 + 3 ^ 40 * 3020300 * 2
def baseEnd_3020300 : Nat := 344636804616586288013311

theorem tailTrace_3020300 : CollatzResearch.WordTrace tailWord_3020300 prefixEnd_3020300 344636804616586288013311 := by
  unfold tailWord_3020300
  simp only [CollatzResearch.WordTrace]
  refine ⟨55079695478988200509045177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73439593971984267345393569 55079695478988200509045177)
  ·
    refine ⟨41309771609241150381783883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55079695478988200509045177 41309771609241150381783883)
    ·
      refine ⟨61964657413861725572675825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41309771609241150381783883 61964657413861725572675825)
      ·
        refine ⟨46473493060396294179506869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61964657413861725572675825 46473493060396294179506869)
        ·
          refine ⟨4356889974412152579328769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46473493060396294179506869 4356889974412152579328769)
          ·
            refine ⟨3267667480809114434496577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4356889974412152579328769 3267667480809114434496577)
            ·
              refine ⟨2450750610606835825872433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3267667480809114434496577 2450750610606835825872433)
              ·
                refine ⟨1838062957955126869404325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2450750610606835825872433 1838062957955126869404325)
                ·
                  refine ⟨344636804616586288013311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1838062957955126869404325 344636804616586288013311)
                  ·
                    rfl

theorem cell22_3020300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_3020300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020300 prefixEnd_3020300 := by exact prefixLift 3020300
  have htrace : WordTrace (prefixWord ++ tailWord_3020300) baseStart_3020300 baseEnd_3020300 := by
    simpa [prefixWord, tailWord_3020300, baseEnd_3020300] using wordTrace_append hprefix tailTrace_3020300
  have hstable : (prefixWord ++ tailWord_3020300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020300).length < 2 ^ (prefixWord ++ tailWord_3020300).sum := by decide
  have hdescent : baseEnd_3020300 < baseStart_3020300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020328 : List Nat := [2, 1, 5, 2, 2, 1, 3, 6]
def baseStart_3020328 : Nat := 118140960795 + 3020328 * 2 ^ 59
def prefixEnd_3020328 : Nat := 4983230072969 + 3 ^ 40 * 3020328 * 2
def baseEnd_3020328 : Nat := 114879999869108458259983

theorem tailTrace_3020328 : CollatzResearch.WordTrace tailWord_3020328 prefixEnd_3020328 114879999869108458259983 := by
  unfold tailWord_3020328
  simp only [CollatzResearch.WordTrace]
  refine ⟨55080206100937480900054819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73440274801249974533406425 55080206100937480900054819)
  ·
    refine ⟨82620309151406221350082229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55080206100937480900054819 82620309151406221350082229)
    ·
      refine ⟨7745653982944333251570209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82620309151406221350082229 7745653982944333251570209)
      ·
        refine ⟨5809240487208249938677657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7745653982944333251570209 5809240487208249938677657)
        ·
          refine ⟨4356930365406187454008243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5809240487208249938677657 4356930365406187454008243)
          ·
            refine ⟨6535395548109281181012365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356930365406187454008243 6535395548109281181012365)
            ·
              refine ⟨2450773330540980442879637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6535395548109281181012365 2450773330540980442879637)
              ·
                refine ⟨114879999869108458259983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2450773330540980442879637 114879999869108458259983)
                ·
                  rfl

theorem cell22_3020328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 6].length) (baseStart_3020328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020328 prefixEnd_3020328 := by exact prefixLift 3020328
  have htrace : WordTrace (prefixWord ++ tailWord_3020328) baseStart_3020328 baseEnd_3020328 := by
    simpa [prefixWord, tailWord_3020328, baseEnd_3020328] using wordTrace_append hprefix tailTrace_3020328
  have hstable : (prefixWord ++ tailWord_3020328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020328).length < 2 ^ (prefixWord ++ tailWord_3020328).sum := by decide
  have hdescent : baseEnd_3020328 < baseStart_3020328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020343 : List Nat := [1, 1, 3, 1, 2, 4, 1, 5, 1, 3]
def baseStart_3020343 : Nat := 118140960795 + 3020343 * 2 ^ 59
def prefixEnd_3020343 : Nat := 4983230072969 + 3 ^ 40 * 3020343 * 2
def baseEnd_3020343 : Nat := 1033925133628521085214801

theorem tailTrace_3020343 : CollatzResearch.WordTrace tailWord_3020343 prefixEnd_3020343 1033925133628521085214801 := by
  unfold tailWord_3020343
  simp only [CollatzResearch.WordTrace]
  refine ⟨110160959296820619361905683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73440639531213746241270455 110160959296820619361905683)
  ·
    refine ⟨165241438945230929042858525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110160959296820619361905683 165241438945230929042858525)
    ·
      refine ⟨61965539604461598391071947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165241438945230929042858525 61965539604461598391071947)
      ·
        refine ⟨92948309406692397586607921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61965539604461598391071947 92948309406692397586607921)
        ·
          refine ⟨69711232055019298189955941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92948309406692397586607921 69711232055019298189955941)
          ·
            refine ⟨13070856010316118410616739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69711232055019298189955941 13070856010316118410616739)
            ·
              refine ⟨19606284015474177615925109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13070856010316118410616739 19606284015474177615925109)
              ·
                refine ⟨1838089126450704151492979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19606284015474177615925109 1838089126450704151492979)
                ·
                  refine ⟨2757133689676056227239469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838089126450704151492979 2757133689676056227239469)
                  ·
                    refine ⟨1033925133628521085214801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757133689676056227239469 1033925133628521085214801)
                    ·
                      rfl

theorem cell22_3020343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_3020343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020343 prefixEnd_3020343 := by exact prefixLift 3020343
  have htrace : WordTrace (prefixWord ++ tailWord_3020343) baseStart_3020343 baseEnd_3020343 := by
    simpa [prefixWord, tailWord_3020343, baseEnd_3020343] using wordTrace_append hprefix tailTrace_3020343
  have hstable : (prefixWord ++ tailWord_3020343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020343).length < 2 ^ (prefixWord ++ tailWord_3020343).sum := by decide
  have hdescent : baseEnd_3020343 < baseStart_3020343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020399 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 3, 5]
def baseStart_3020399 : Nat := 118140960795 + 3020399 * 2 ^ 59
def prefixEnd_3020399 : Nat := 4983230072969 + 3 ^ 40 * 3020399 * 2
def baseEnd_3020399 : Nat := 1033944303572955605814629

theorem tailTrace_3020399 : CollatzResearch.WordTrace tailWord_3020399 prefixEnd_3020399 1033944303572955605814629 := by
  unfold tailWord_3020399
  simp only [CollatzResearch.WordTrace]
  refine ⟨110163001784617740925944251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73442001189745160617296167 110163001784617740925944251)
  ·
    refine ⟨165244502676926611388916377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110163001784617740925944251 165244502676926611388916377)
    ·
      refine ⟨123933377007694958541687283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165244502676926611388916377 123933377007694958541687283)
      ·
        refine ⟨185900065511542437812530925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123933377007694958541687283 185900065511542437812530925)
        ·
          refine ⟨69712524566828414179699097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185900065511542437812530925 69712524566828414179699097)
          ·
            refine ⟨52284393425121310634774323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69712524566828414179699097 52284393425121310634774323)
            ·
              refine ⟨78426590137681965952161485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52284393425121310634774323 78426590137681965952161485)
              ·
                refine ⟨29409971301630737232060557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78426590137681965952161485 29409971301630737232060557)
                ·
                  refine ⟨11028739238111526462022709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29409971301630737232060557 11028739238111526462022709)
                  ·
                    refine ⟨1033944303572955605814629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11028739238111526462022709 1033944303572955605814629)
                    ·
                      rfl

theorem cell22_3020399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_3020399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020399 prefixEnd_3020399 := by exact prefixLift 3020399
  have htrace : WordTrace (prefixWord ++ tailWord_3020399) baseStart_3020399 baseEnd_3020399 := by
    simpa [prefixWord, tailWord_3020399, baseEnd_3020399] using wordTrace_append hprefix tailTrace_3020399
  have hstable : (prefixWord ++ tailWord_3020399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020399).length < 2 ^ (prefixWord ++ tailWord_3020399).sum := by decide
  have hdescent : baseEnd_3020399 < baseStart_3020399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020416 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 4, 3]
def baseStart_3020416 : Nat := 118140960795 + 3020416 * 2 ^ 59
def prefixEnd_3020416 : Nat := 4983230072969 + 3 ^ 40 * 3020416 * 2
def baseEnd_3020416 : Nat := 1033950123020373228139577

theorem tailTrace_3020416 : CollatzResearch.WordTrace tailWord_3020416 prefixEnd_3020416 1033950123020373228139577 := by
  unfold tailWord_3020416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55081810912778076414656551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73442414550370768552875401 55081810912778076414656551)
  ·
    refine ⟨82622716369167114621984827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55081810912778076414656551 82622716369167114621984827)
    ·
      refine ⟨123934074553750671932977241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82622716369167114621984827 123934074553750671932977241)
      ·
        refine ⟨92950555915313003949732931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123934074553750671932977241 92950555915313003949732931)
        ·
          refine ⟨139425833872969505924599397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92950555915313003949732931 139425833872969505924599397)
          ·
            refine ⟨26142343851181782360862387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139425833872969505924599397 26142343851181782360862387)
            ·
              refine ⟨39213515776772673541293581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26142343851181782360862387 39213515776772673541293581)
              ·
                refine ⟨14705068416289752577985093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39213515776772673541293581 14705068416289752577985093)
                ·
                  refine ⟨2757200328054328608372205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14705068416289752577985093 2757200328054328608372205)
                  ·
                    refine ⟨1033950123020373228139577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757200328054328608372205 1033950123020373228139577)
                    ·
                      rfl

theorem cell22_3020416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_3020416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020416 prefixEnd_3020416 := by exact prefixLift 3020416
  have htrace : WordTrace (prefixWord ++ tailWord_3020416) baseStart_3020416 baseEnd_3020416 := by
    simpa [prefixWord, tailWord_3020416, baseEnd_3020416] using wordTrace_append hprefix tailTrace_3020416
  have hstable : (prefixWord ++ tailWord_3020416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020416).length < 2 ^ (prefixWord ++ tailWord_3020416).sum := by decide
  have hdescent : baseEnd_3020416 < baseStart_3020416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020448 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_3020448 : Nat := 118140960795 + 3020448 * 2 ^ 59
def prefixEnd_3020448 : Nat := 4983230072969 + 3 ^ 40 * 3020448 * 2
def baseEnd_3020448 : Nat := 1033961077274335811339479

theorem tailTrace_3020448 : CollatzResearch.WordTrace tailWord_3020448 prefixEnd_3020448 1033961077274335811339479 := by
  unfold tailWord_3020448
  simp only [CollatzResearch.WordTrace]
  refine ⟨55082394480720111147238999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73443192640960148196318665 55082394480720111147238999)
  ·
    refine ⟨82623591721080166720858499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55082394480720111147238999 82623591721080166720858499)
    ·
      refine ⟨123935387581620250081287749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82623591721080166720858499 123935387581620250081287749)
      ·
        refine ⟨23237885171553796890241453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123935387581620250081287749 23237885171553796890241453)
        ·
          refine ⟨8714206939332673833840545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23237885171553796890241453 8714206939332673833840545)
          ·
            refine ⟨6535655204499505375380409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8714206939332673833840545 6535655204499505375380409)
            ·
              refine ⟨4901741403374629031535307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6535655204499505375380409 4901741403374629031535307)
              ·
                refine ⟨7352612105061943547302961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901741403374629031535307 7352612105061943547302961)
                ·
                  refine ⟨5514459078796457660477221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7352612105061943547302961 5514459078796457660477221)
                  ·
                    refine ⟨1033961077274335811339479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5514459078796457660477221 1033961077274335811339479)
                    ·
                      rfl

theorem cell22_3020448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_3020448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020448 prefixEnd_3020448 := by exact prefixLift 3020448
  have htrace : WordTrace (prefixWord ++ tailWord_3020448) baseStart_3020448 baseEnd_3020448 := by
    simpa [prefixWord, tailWord_3020448, baseEnd_3020448] using wordTrace_append hprefix tailTrace_3020448
  have hstable : (prefixWord ++ tailWord_3020448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020448).length < 2 ^ (prefixWord ++ tailWord_3020448).sum := by decide
  have hdescent : baseEnd_3020448 < baseStart_3020448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020450 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3020450 : Nat := 118140960795 + 3020450 * 2 ^ 59
def prefixEnd_3020450 : Nat := 4983230072969 + 3 ^ 40 * 3020450 * 2
def baseEnd_3020450 : Nat := 1033961761915208472789473

theorem tailTrace_3020450 : CollatzResearch.WordTrace tailWord_3020450 prefixEnd_3020450 1033961761915208472789473 := by
  unfold tailWord_3020450
  simp only [CollatzResearch.WordTrace]
  refine ⟨27541215476858244159012701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73443241271621984424033869 27541215476858244159012701)
  ·
    refine ⟨10327955803821841559629763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27541215476858244159012701 10327955803821841559629763)
    ·
      refine ⟨15491933705732762339444645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10327955803821841559629763 15491933705732762339444645)
      ·
        refine ⟨2904737569824892938645871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15491933705732762339444645 2904737569824892938645871)
        ·
          refine ⟨4357106354737339407968807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2904737569824892938645871 4357106354737339407968807)
          ·
            refine ⟨6535659532106009111953211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357106354737339407968807 6535659532106009111953211)
            ·
              refine ⟨9803489298159013667929817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535659532106009111953211 9803489298159013667929817)
              ·
                refine ⟨7352616973619260250947363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9803489298159013667929817 7352616973619260250947363)
                ·
                  refine ⟨11028925460428890376421045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7352616973619260250947363 11028925460428890376421045)
                  ·
                    refine ⟨1033961761915208472789473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11028925460428890376421045 1033961761915208472789473)
                    ·
                      rfl

theorem cell22_3020450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3020450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020450 prefixEnd_3020450 := by exact prefixLift 3020450
  have htrace : WordTrace (prefixWord ++ tailWord_3020450) baseStart_3020450 baseEnd_3020450 := by
    simpa [prefixWord, tailWord_3020450, baseEnd_3020450] using wordTrace_append hprefix tailTrace_3020450
  have hstable : (prefixWord ++ tailWord_3020450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020450).length < 2 ^ (prefixWord ++ tailWord_3020450).sum := by decide
  have hdescent : baseEnd_3020450 < baseStart_3020450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020469 : List Nat := [1, 3, 3, 3, 3, 1, 2, 2, 4]
def baseStart_3020469 : Nat := 118140960795 + 3020469 * 2 ^ 59
def prefixEnd_3020469 : Nat := 4983230072969 + 3 ^ 40 * 3020469 * 2
def baseEnd_3020469 : Nat := 344656088667832918854805

theorem tailTrace_3020469 : CollatzResearch.WordTrace tailWord_3020469 prefixEnd_3020469 344656088667832918854805 := by
  unfold tailWord_3020469
  simp only [CollatzResearch.WordTrace]
  refine ⟨110165554894364142880992461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73443703262909428587328307 110165554894364142880992461)
  ·
    refine ⟨41312083085386553580372173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110165554894364142880992461 41312083085386553580372173)
    ·
      refine ⟨15492031157019957592639565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41312083085386553580372173 15492031157019957592639565)
      ·
        refine ⟨5809511683882484097239837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15492031157019957592639565 5809511683882484097239837)
        ·
          refine ⟨2178566881455931536464939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5809511683882484097239837 2178566881455931536464939)
          ·
            refine ⟨3267850322183897304697409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178566881455931536464939 3267850322183897304697409)
            ·
              refine ⟨2450887741637922978523057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3267850322183897304697409 2450887741637922978523057)
              ·
                refine ⟨1838165806228442233892293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2450887741637922978523057 1838165806228442233892293)
                ·
                  refine ⟨344656088667832918854805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1838165806228442233892293 344656088667832918854805)
                  ·
                    rfl

theorem cell22_3020469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_3020469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020469 prefixEnd_3020469 := by exact prefixLift 3020469
  have htrace : WordTrace (prefixWord ++ tailWord_3020469) baseStart_3020469 baseEnd_3020469 := by
    simpa [prefixWord, tailWord_3020469, baseEnd_3020469] using wordTrace_append hprefix tailTrace_3020469
  have hstable : (prefixWord ++ tailWord_3020469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020469).length < 2 ^ (prefixWord ++ tailWord_3020469).sum := by decide
  have hdescent : baseEnd_3020469 < baseStart_3020469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020476 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_3020476 : Nat := 118140960795 + 3020476 * 2 ^ 59
def prefixEnd_3020476 : Nat := 4983230072969 + 3 ^ 40 * 3020476 * 2
def baseEnd_3020476 : Nat := 1033970662246553071639393

theorem tailTrace_3020476 : CollatzResearch.WordTrace tailWord_3020476 prefixEnd_3020476 1033970662246553071639393 := by
  unfold tailWord_3020476
  simp only [CollatzResearch.WordTrace]
  refine ⟨55082905102669391538248641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73443873470225855384331521 55082905102669391538248641)
  ·
    refine ⟨41312178827002043653686481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55082905102669391538248641 41312178827002043653686481)
    ·
      refine ⟨30984134120251532740264861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41312178827002043653686481 30984134120251532740264861)
      ·
        refine ⟨11619050295094324777599323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30984134120251532740264861 11619050295094324777599323)
        ·
          refine ⟨17428575442641487166398985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11619050295094324777599323 17428575442641487166398985)
          ·
            refine ⟨13071431581981115374799239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17428575442641487166398985 13071431581981115374799239)
            ·
              refine ⟨19607147372971673062198859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13071431581981115374799239 19607147372971673062198859)
              ·
                refine ⟨29410721059457509593298289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19607147372971673062198859 29410721059457509593298289)
                ·
                  refine ⟨22058040794593132194973717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29410721059457509593298289 22058040794593132194973717)
                  ·
                    refine ⟨1033970662246553071639393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22058040794593132194973717 1033970662246553071639393)
                    ·
                      rfl

theorem cell22_3020476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_3020476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020476 prefixEnd_3020476 := by exact prefixLift 3020476
  have htrace : WordTrace (prefixWord ++ tailWord_3020476) baseStart_3020476 baseEnd_3020476 := by
    simpa [prefixWord, tailWord_3020476, baseEnd_3020476] using wordTrace_append hprefix tailTrace_3020476
  have hstable : (prefixWord ++ tailWord_3020476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020476).length < 2 ^ (prefixWord ++ tailWord_3020476).sum := by decide
  have hdescent : baseEnd_3020476 < baseStart_3020476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020525 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 5]
def baseStart_3020525 : Nat := 118140960795 + 3020525 * 2 ^ 59
def prefixEnd_3020525 : Nat := 4983230072969 + 3 ^ 40 * 3020525 * 2
def baseEnd_3020525 : Nat := 344662478649311092388081

theorem tailTrace_3020525 : CollatzResearch.WordTrace tailWord_3020525 prefixEnd_3020525 344662478649311092388081 := by
  unfold tailWord_3020525
  simp only [CollatzResearch.WordTrace]
  refine ⟨110167597382161264445031029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73445064921440842963354019 110167597382161264445031029)
  ·
    refine ⟨10328212254577618541721659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110167597382161264445031029 10328212254577618541721659)
    ·
      refine ⟨15492318381866427812582489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10328212254577618541721659 15492318381866427812582489)
      ·
        refine ⟨11619238786399820859436867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15492318381866427812582489 11619238786399820859436867)
        ·
          refine ⟨17428858179599731289155301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11619238786399820859436867 17428858179599731289155301)
          ·
            refine ⟨3267910908674949616716619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17428858179599731289155301 3267910908674949616716619)
            ·
              refine ⟨4901866363012424425074929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267910908674949616716619 4901866363012424425074929)
              ·
                refine ⟨3676399772259318318806197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901866363012424425074929 3676399772259318318806197)
                ·
                  refine ⟨344662478649311092388081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3676399772259318318806197 344662478649311092388081)
                  ·
                    rfl

theorem cell22_3020525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_3020525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020525 prefixEnd_3020525 := by exact prefixLift 3020525
  have htrace : WordTrace (prefixWord ++ tailWord_3020525) baseStart_3020525 baseEnd_3020525 := by
    simpa [prefixWord, tailWord_3020525, baseEnd_3020525] using wordTrace_append hprefix tailTrace_3020525
  have hstable : (prefixWord ++ tailWord_3020525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020525).length < 2 ^ (prefixWord ++ tailWord_3020525).sum := by decide
  have hdescent : baseEnd_3020525 < baseStart_3020525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020542 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3020542 : Nat := 118140960795 + 3020542 * 2 ^ 59
def prefixEnd_3020542 : Nat := 4983230072969 + 3 ^ 40 * 3020542 * 2
def baseEnd_3020542 : Nat := 344664418465116966496397

theorem tailTrace_3020542 : CollatzResearch.WordTrace tailWord_3020542 prefixEnd_3020542 344664418465116966496397 := by
  unfold tailWord_3020542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13771027177887459543549985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73445478282066450898933253 13771027177887459543549985)
  ·
    refine ⟨10328270383415594657662489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13771027177887459543549985 10328270383415594657662489)
    ·
      refine ⟨7746202787561695993246867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10328270383415594657662489 7746202787561695993246867)
      ·
        refine ⟨11619304181342543989870301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7746202787561695993246867 11619304181342543989870301)
        ·
          refine ⟨4357239068003453996201363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11619304181342543989870301 4357239068003453996201363)
          ·
            refine ⟨6535858602005180994302045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357239068003453996201363 6535858602005180994302045)
            ·
              refine ⟨2450946975751942872863267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6535858602005180994302045 2450946975751942872863267)
              ·
                refine ⟨3676420463627914309294901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450946975751942872863267 3676420463627914309294901)
                ·
                  refine ⟨344664418465116966496397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3676420463627914309294901 344664418465116966496397)
                  ·
                    rfl

theorem cell22_3020542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3020542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020542 prefixEnd_3020542 := by exact prefixLift 3020542
  have htrace : WordTrace (prefixWord ++ tailWord_3020542) baseStart_3020542 baseEnd_3020542 := by
    simpa [prefixWord, tailWord_3020542, baseEnd_3020542] using wordTrace_append hprefix tailTrace_3020542
  have hstable : (prefixWord ++ tailWord_3020542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020542).length < 2 ^ (prefixWord ++ tailWord_3020542).sum := by decide
  have hdescent : baseEnd_3020542 < baseStart_3020542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020568 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 4, 3]
def baseStart_3020568 : Nat := 118140960795 + 3020568 * 2 ^ 59
def prefixEnd_3020568 : Nat := 4983230072969 + 3 ^ 40 * 3020568 * 2
def baseEnd_3020568 : Nat := 1034002155726695498339111

theorem tailTrace_3020568 : CollatzResearch.WordTrace tailWord_3020568 prefixEnd_3020568 1034002155726695498339111 := by
  unfold tailWord_3020568
  simp only [CollatzResearch.WordTrace]
  refine ⟨55084582860502741394423179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73446110480670321859230905 55084582860502741394423179)
  ·
    refine ⟨82626874290754112091634769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55084582860502741394423179 82626874290754112091634769)
    ·
      refine ⟨61970155718065584068726077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82626874290754112091634769 61970155718065584068726077)
      ·
        refine ⟨23238808394274594025772279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61970155718065584068726077 23238808394274594025772279)
        ·
          refine ⟨34858212591411891038658419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23238808394274594025772279 34858212591411891038658419)
          ·
            refine ⟨52287318887117836557987629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34858212591411891038658419 52287318887117836557987629)
            ·
              refine ⟨19607744582669188709245361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52287318887117836557987629 19607744582669188709245361)
              ·
                refine ⟨14705808437001891531934021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19607744582669188709245361 14705808437001891531934021)
                ·
                  refine ⟨2757339081937854662237629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14705808437001891531934021 2757339081937854662237629)
                  ·
                    refine ⟨1034002155726695498339111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757339081937854662237629 1034002155726695498339111)
                    ·
                      rfl

theorem cell22_3020568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_3020568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020568 prefixEnd_3020568 := by exact prefixLift 3020568
  have htrace : WordTrace (prefixWord ++ tailWord_3020568) baseStart_3020568 baseEnd_3020568 := by
    simpa [prefixWord, tailWord_3020568, baseEnd_3020568] using wordTrace_append hprefix tailTrace_3020568
  have hstable : (prefixWord ++ tailWord_3020568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020568).length < 2 ^ (prefixWord ++ tailWord_3020568).sum := by decide
  have hdescent : baseEnd_3020568 < baseStart_3020568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020570 : List Nat := [3, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_3020570 : Nat := 118140960795 + 3020570 * 2 ^ 59
def prefixEnd_3020570 : Nat := 4983230072969 + 3 ^ 40 * 3020570 * 2
def baseEnd_3020570 : Nat := 344667613455856053263035

theorem tailTrace_3020570 : CollatzResearch.WordTrace tailWord_3020570 prefixEnd_3020570 344667613455856053263035 := by
  unfold tailWord_3020570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27542309666749559282604791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73446159111332158086946109 27542309666749559282604791)
  ·
    refine ⟨41313464500124338923907187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27542309666749559282604791 41313464500124338923907187)
    ·
      refine ⟨61970196750186508385860781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41313464500124338923907187 61970196750186508385860781)
      ·
        refine ⟨23238823781319940644697793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61970196750186508385860781 23238823781319940644697793)
        ·
          refine ⟨17429117835989955483523345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23238823781319940644697793 17429117835989955483523345)
          ·
            refine ⟨13071838376992466612642509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17429117835989955483523345 13071838376992466612642509)
            ·
              refine ⟨4901939391372174979740941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13071838376992466612642509 4901939391372174979740941)
              ·
                refine ⟨1838227271764565617402853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4901939391372174979740941 1838227271764565617402853)
                ·
                  refine ⟨344667613455856053263035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1838227271764565617402853 344667613455856053263035)
                  ·
                    rfl

theorem cell22_3020570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_3020570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020570 prefixEnd_3020570 := by exact prefixLift 3020570
  have htrace : WordTrace (prefixWord ++ tailWord_3020570) baseStart_3020570 baseEnd_3020570 := by
    simpa [prefixWord, tailWord_3020570, baseEnd_3020570] using wordTrace_append hprefix tailTrace_3020570
  have hstable : (prefixWord ++ tailWord_3020570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020570).length < 2 ^ (prefixWord ++ tailWord_3020570).sum := by decide
  have hdescent : baseEnd_3020570 < baseStart_3020570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020581 : List Nat := [1, 3, 1, 2, 3, 2, 10]
def baseStart_3020581 : Nat := 118140960795 + 3020581 * 2 ^ 59
def prefixEnd_3020581 : Nat := 4983230072969 + 3 ^ 40 * 3020581 * 2
def baseEnd_3020581 : Nat := 38296540958976585102373

theorem tailTrace_3020581 : CollatzResearch.WordTrace tailWord_3020581 prefixEnd_3020581 38296540958976585102373 := by
  unfold tailWord_3020581
  simp only [CollatzResearch.WordTrace]
  refine ⟨110169639869958386009069597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73446426579972257339379731 110169639869958386009069597)
  ·
    refine ⟨41313614951234394753401099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110169639869958386009069597 41313614951234394753401099)
    ·
      refine ⟨61970422426851592130101649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41313614951234394753401099 61970422426851592130101649)
      ·
        refine ⟨46477816820138694097576237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61970422426851592130101649 46477816820138694097576237)
        ·
          refine ⟨17429181307552010286591089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46477816820138694097576237 17429181307552010286591089)
          ·
            refine ⟨13071885980664007714943317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17429181307552010286591089 13071885980664007714943317)
            ·
              refine ⟨38296540958976585102373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13071885980664007714943317 38296540958976585102373)
              ·
                rfl

theorem cell22_3020581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 10].length) (baseStart_3020581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020581 prefixEnd_3020581 := by exact prefixLift 3020581
  have htrace : WordTrace (prefixWord ++ tailWord_3020581) baseStart_3020581 baseEnd_3020581 := by
    simpa [prefixWord, tailWord_3020581, baseEnd_3020581] using wordTrace_append hprefix tailTrace_3020581
  have hstable : (prefixWord ++ tailWord_3020581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020581).length < 2 ^ (prefixWord ++ tailWord_3020581).sum := by decide
  have hdescent : baseEnd_3020581 < baseStart_3020581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020602 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_3020602 : Nat := 118140960795 + 3020602 * 2 ^ 59
def prefixEnd_3020602 : Nat := 4983230072969 + 3 ^ 40 * 3020602 * 2
def baseEnd_3020602 : Nat := 1034013794621530742989007

theorem tailTrace_3020602 : CollatzResearch.WordTrace tailWord_3020602 prefixEnd_3020602 1034013794621530742989007 := by
  unfold tailWord_3020602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27542601450720576648896015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73446937201921537730389373 27542601450720576648896015)
  ·
    refine ⟨41313902176080864973344023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27542601450720576648896015 41313902176080864973344023)
    ·
      refine ⟨61970853264121297460016035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41313902176080864973344023 61970853264121297460016035)
      ·
        refine ⟨92956279896181946190024053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61970853264121297460016035 92956279896181946190024053)
        ·
          refine ⟨8714651240267057455314755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92956279896181946190024053 8714651240267057455314755)
          ·
            refine ⟨13071976860400586182972133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8714651240267057455314755 13071976860400586182972133)
            ·
              refine ⟨2450995661325109909307275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13071976860400586182972133 2450995661325109909307275)
              ·
                refine ⟨3676493491987664863960913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450995661325109909307275 3676493491987664863960913)
                ·
                  refine ⟨2757370118990748647970685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676493491987664863960913 2757370118990748647970685)
                  ·
                    refine ⟨1034013794621530742989007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757370118990748647970685 1034013794621530742989007)
                    ·
                      rfl

theorem cell22_3020602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_3020602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020602 prefixEnd_3020602 := by exact prefixLift 3020602
  have htrace : WordTrace (prefixWord ++ tailWord_3020602) baseStart_3020602 baseEnd_3020602 := by
    simpa [prefixWord, tailWord_3020602, baseEnd_3020602] using wordTrace_append hprefix tailTrace_3020602
  have hstable : (prefixWord ++ tailWord_3020602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020602).length < 2 ^ (prefixWord ++ tailWord_3020602).sum := by decide
  have hdescent : baseEnd_3020602 < baseStart_3020602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020613 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_3020613 : Nat := 118140960795 + 3020613 * 2 ^ 59
def prefixEnd_3020613 : Nat := 4983230072969 + 3 ^ 40 * 3020613 * 2
def baseEnd_3020613 : Nat := 1034017560146330380963973

theorem tailTrace_3020613 : CollatzResearch.WordTrace tailWord_3020613 prefixEnd_3020613 1034017560146330380963973 := by
  unfold tailWord_3020613
  simp only [CollatzResearch.WordTrace]
  refine ⟨110170807005842455474234493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73447204670561636982822995 110170807005842455474234493)
  ·
    refine ⟨41314052627190920802837935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110170807005842455474234493 41314052627190920802837935)
    ·
      refine ⟨61971078940786381204256903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41314052627190920802837935 61971078940786381204256903)
      ·
        refine ⟨92956618411179571806385355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61971078940786381204256903 92956618411179571806385355)
        ·
          refine ⟨139434927616769357709578033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92956618411179571806385355 139434927616769357709578033)
          ·
            refine ⟨104576195712577018282183525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139434927616769357709578033 104576195712577018282183525)
            ·
              refine ⟨19608036696108190927909411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104576195712577018282183525 19608036696108190927909411)
              ·
                refine ⟨29412055044162286391864117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19608036696108190927909411 29412055044162286391864117)
                ·
                  refine ⟨2757380160390214349237261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29412055044162286391864117 2757380160390214349237261)
                  ·
                    refine ⟨1034017560146330380963973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757380160390214349237261 1034017560146330380963973)
                    ·
                      rfl

theorem cell22_3020613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_3020613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020613 prefixEnd_3020613 := by exact prefixLift 3020613
  have htrace : WordTrace (prefixWord ++ tailWord_3020613) baseStart_3020613 baseEnd_3020613 := by
    simpa [prefixWord, tailWord_3020613, baseEnd_3020613] using wordTrace_append hprefix tailTrace_3020613
  have hstable : (prefixWord ++ tailWord_3020613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020613).length < 2 ^ (prefixWord ++ tailWord_3020613).sum := by decide
  have hdescent : baseEnd_3020613 < baseStart_3020613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020647 : List Nat := [1, 1, 5, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3020647 : Nat := 118140960795 + 3020647 * 2 ^ 59
def prefixEnd_3020647 : Nat := 4983230072969 + 3 ^ 40 * 3020647 * 2
def baseEnd_3020647 : Nat := 1034029199041165625613869

theorem tailTrace_3020647 : CollatzResearch.WordTrace tailWord_3020647 prefixEnd_3020647 1034029199041165625613869 := by
  unfold tailWord_3020647
  simp only [CollatzResearch.WordTrace]
  refine ⟨110172047087719279280972195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73448031391812852853981463 110172047087719279280972195)
  ·
    refine ⟨165258070631578918921458293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110172047087719279280972195 165258070631578918921458293)
    ·
      refine ⟨15492944121710523648886715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165258070631578918921458293 15492944121710523648886715)
      ·
        refine ⟨23239416182565785473330073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15492944121710523648886715 23239416182565785473330073)
        ·
          refine ⟨17429562136924339104997555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23239416182565785473330073 17429562136924339104997555)
          ·
            refine ⟨26144343205386508657496333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17429562136924339104997555 26144343205386508657496333)
            ·
              refine ⟨9804128702019940746561125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26144343205386508657496333 9804128702019940746561125)
              ·
                refine ⟨1838274131628738889980211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9804128702019940746561125 1838274131628738889980211)
                ·
                  refine ⟨2757411197443108334970317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838274131628738889980211 2757411197443108334970317)
                  ·
                    refine ⟨1034029199041165625613869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757411197443108334970317 1034029199041165625613869)
                    ·
                      rfl

theorem cell22_3020647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3020647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020647 prefixEnd_3020647 := by exact prefixLift 3020647
  have htrace : WordTrace (prefixWord ++ tailWord_3020647) baseStart_3020647 baseEnd_3020647 := by
    simpa [prefixWord, tailWord_3020647, baseEnd_3020647] using wordTrace_append hprefix tailTrace_3020647
  have hstable : (prefixWord ++ tailWord_3020647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020647).length < 2 ^ (prefixWord ++ tailWord_3020647).sum := by decide
  have hdescent : baseEnd_3020647 < baseStart_3020647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020694 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3020694 : Nat := 118140960795 + 3020694 * 2 ^ 59
def prefixEnd_3020694 : Nat := 4983230072969 + 3 ^ 40 * 3020694 * 2
def baseEnd_3020694 : Nat := 344681762700557723229575

theorem tailTrace_3020694 : CollatzResearch.WordTrace tailWord_3020694 prefixEnd_3020694 344681762700557723229575 := by
  unfold tailWord_3020694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6885860082409312894245821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73449174212366004205288757 6885860082409312894245821)
  ·
    refine ⟨2582197530903492335342183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6885860082409312894245821 2582197530903492335342183)
    ·
      refine ⟨3873296296355238503013275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2582197530903492335342183 3873296296355238503013275)
      ·
        refine ⟨5809944444532857754519913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873296296355238503013275 5809944444532857754519913)
        ·
          refine ⟨4357458333399643315889935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5809944444532857754519913 4357458333399643315889935)
          ·
            refine ⟨6536187500099464973834903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357458333399643315889935 6536187500099464973834903)
            ·
              refine ⟨9804281250149197460752355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536187500099464973834903 9804281250149197460752355)
              ·
                refine ⟨14706421875223796191128533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9804281250149197460752355 14706421875223796191128533)
                ·
                  refine ⟨344681762700557723229575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14706421875223796191128533 344681762700557723229575)
                  ·
                    rfl

theorem cell22_3020694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3020694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020694 prefixEnd_3020694 := by exact prefixLift 3020694
  have htrace : WordTrace (prefixWord ++ tailWord_3020694) baseStart_3020694 baseEnd_3020694 := by
    simpa [prefixWord, tailWord_3020694, baseEnd_3020694] using wordTrace_append hprefix tailTrace_3020694
  have hstable : (prefixWord ++ tailWord_3020694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020694).length < 2 ^ (prefixWord ++ tailWord_3020694).sum := by decide
  have hdescent : baseEnd_3020694 < baseStart_3020694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020842 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3020842 : Nat := 118140960795 + 3020842 * 2 ^ 59
def prefixEnd_3020842 : Nat := 4983230072969 + 3 ^ 40 * 3020842 * 2
def baseEnd_3020842 : Nat := 1034095951526250116988271

theorem tailTrace_3020842 : CollatzResearch.WordTrace tailWord_3020842 prefixEnd_3020842 1034095951526250116988271 := by
  unfold tailWord_3020842
  simp only [CollatzResearch.WordTrace]
  refine ⟨27544789830503206896080195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73452772881341885056213853 27544789830503206896080195)
  ·
    refine ⟨41317184745754810344120293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27544789830503206896080195 41317184745754810344120293)
    ·
      refine ⟨7746972139829026939522555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41317184745754810344120293 7746972139829026939522555)
      ·
        refine ⟨11620458209743540409283833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7746972139829026939522555 11620458209743540409283833)
        ·
          refine ⟨8715343657307655306962875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11620458209743540409283833 8715343657307655306962875)
          ·
            refine ⟨13073015485961482960444313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8715343657307655306962875 13073015485961482960444313)
            ·
              refine ⟨9804761614471112220333235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13073015485961482960444313 9804761614471112220333235)
              ·
                refine ⟨14707142421706668330499853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9804761614471112220333235 14707142421706668330499853)
                ·
                  refine ⟨5515178408140000623937445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14707142421706668330499853 5515178408140000623937445)
                  ·
                    refine ⟨1034095951526250116988271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5515178408140000623937445 1034095951526250116988271)
                    ·
                      rfl

theorem cell22_3020842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3020842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020842 prefixEnd_3020842 := by exact prefixLift 3020842
  have htrace : WordTrace (prefixWord ++ tailWord_3020842) baseStart_3020842 baseEnd_3020842 := by
    simpa [prefixWord, tailWord_3020842, baseEnd_3020842] using wordTrace_append hprefix tailTrace_3020842
  have hstable : (prefixWord ++ tailWord_3020842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020842).length < 2 ^ (prefixWord ++ tailWord_3020842).sum := by decide
  have hdescent : baseEnd_3020842 < baseStart_3020842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020855 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 1, 5]
def baseStart_3020855 : Nat := 118140960795 + 3020855 * 2 ^ 59
def prefixEnd_3020855 : Nat := 4983230072969 + 3 ^ 40 * 3020855 * 2
def baseEnd_3020855 : Nat := 1034100401691922416413231

theorem tailTrace_3020855 : CollatzResearch.WordTrace tailWord_3020855 prefixEnd_3020855 1034100401691922416413231 := by
  unfold tailWord_3020855
  simp only [CollatzResearch.WordTrace]
  refine ⟨110179633470965730804544019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73453088980643820536362679 110179633470965730804544019)
  ·
    refine ⟨165269450206448596206816029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110179633470965730804544019 165269450206448596206816029)
    ·
      refine ⟨61976043827418223577556011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165269450206448596206816029 61976043827418223577556011)
      ·
        refine ⟨92964065741127335366334017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61976043827418223577556011 92964065741127335366334017)
        ·
          refine ⟨69723049305845501524750513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92964065741127335366334017 69723049305845501524750513)
          ·
            refine ⟨52292286979384126143562885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69723049305845501524750513 52292286979384126143562885)
            ·
              refine ⟨9804803808634523651918041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52292286979384126143562885 9804803808634523651918041)
              ·
                refine ⟨7353602856475892738938531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9804803808634523651918041 7353602856475892738938531)
                ·
                  refine ⟨11030404284713839108407797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7353602856475892738938531 11030404284713839108407797)
                  ·
                    refine ⟨1034100401691922416413231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11030404284713839108407797 1034100401691922416413231)
                    ·
                      rfl

theorem cell22_3020855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_3020855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020855 prefixEnd_3020855 := by exact prefixLift 3020855
  have htrace : WordTrace (prefixWord ++ tailWord_3020855) baseStart_3020855 baseEnd_3020855 := by
    simpa [prefixWord, tailWord_3020855, baseEnd_3020855] using wordTrace_append hprefix tailTrace_3020855
  have hstable : (prefixWord ++ tailWord_3020855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020855).length < 2 ^ (prefixWord ++ tailWord_3020855).sum := by decide
  have hdescent : baseEnd_3020855 < baseStart_3020855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020872 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 2, 3]
def baseStart_3020872 : Nat := 118140960795 + 3020872 * 2 ^ 59
def prefixEnd_3020872 : Nat := 4983230072969 + 3 ^ 40 * 3020872 * 2
def baseEnd_3020872 : Nat := 1034106221139340038738179

theorem tailTrace_3020872 : CollatzResearch.WordTrace tailWord_3020872 prefixEnd_3020872 1034106221139340038738179 := by
  unfold tailWord_3020872
  simp only [CollatzResearch.WordTrace]
  refine ⟨55090126755952071353956435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73453502341269428471941913 55090126755952071353956435)
  ·
    refine ⟨82635190133928107030934653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55090126755952071353956435 82635190133928107030934653)
    ·
      refine ⟨30988196300223040136600495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82635190133928107030934653 30988196300223040136600495)
      ·
        refine ⟨46482294450334560204900743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30988196300223040136600495 46482294450334560204900743)
        ·
          refine ⟨69723441675501840307351115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46482294450334560204900743 69723441675501840307351115)
          ·
            refine ⟨104585162513252760461026673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69723441675501840307351115 104585162513252760461026673)
            ·
              refine ⟨78438871884939570345770005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104585162513252760461026673 78438871884939570345770005)
              ·
                refine ⟨3676822119606542359957969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78438871884939570345770005 3676822119606542359957969)
                ·
                  refine ⟨2757616589704906769968477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676822119606542359957969 2757616589704906769968477)
                  ·
                    refine ⟨1034106221139340038738179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757616589704906769968477 1034106221139340038738179)
                    ·
                      rfl

theorem cell22_3020872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_3020872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020872 prefixEnd_3020872 := by exact prefixLift 3020872
  have htrace : WordTrace (prefixWord ++ tailWord_3020872) baseStart_3020872 baseEnd_3020872 := by
    simpa [prefixWord, tailWord_3020872, baseEnd_3020872] using wordTrace_append hprefix tailTrace_3020872
  have hstable : (prefixWord ++ tailWord_3020872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020872).length < 2 ^ (prefixWord ++ tailWord_3020872).sum := by decide
  have hdescent : baseEnd_3020872 < baseStart_3020872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020889 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 2, 3]
def baseStart_3020889 : Nat := 118140960795 + 3020889 * 2 ^ 59
def prefixEnd_3020889 : Nat := 4983230072969 + 3 ^ 40 * 3020889 * 2
def baseEnd_3020889 : Nat := 1034112040586757661063127

theorem tailTrace_3020889 : CollatzResearch.WordTrace tailWord_3020889 prefixEnd_3020889 1034112040586757661063127 := by
  unfold tailWord_3020889
  simp only [CollatzResearch.WordTrace]
  refine ⟨110180873552842554611281721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73453915701895036407521147 110180873552842554611281721)
  ·
    refine ⟨82635655164631915958461291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110180873552842554611281721 82635655164631915958461291)
    ·
      refine ⟨123953482746947873937691937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82635655164631915958461291 123953482746947873937691937)
      ·
        refine ⟨92965112060210905453268953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123953482746947873937691937 92965112060210905453268953)
        ·
          refine ⟨69723834045158179089951715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92965112060210905453268953 69723834045158179089951715)
          ·
            refine ⟨104585751067737268634927573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69723834045158179089951715 104585751067737268634927573)
            ·
              refine ⟨2451228540650092233631115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 104585751067737268634927573 2451228540650092233631115)
              ·
                refine ⟨3676842810975138350446673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451228540650092233631115 3676842810975138350446673)
                ·
                  refine ⟨2757632108231353762835005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676842810975138350446673 2757632108231353762835005)
                  ·
                    refine ⟨1034112040586757661063127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757632108231353762835005 1034112040586757661063127)
                    ·
                      rfl

theorem cell22_3020889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 3].length) (baseStart_3020889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020889 prefixEnd_3020889 := by exact prefixLift 3020889
  have htrace : WordTrace (prefixWord ++ tailWord_3020889) baseStart_3020889 baseEnd_3020889 := by
    simpa [prefixWord, tailWord_3020889, baseEnd_3020889] using wordTrace_append hprefix tailTrace_3020889
  have hstable : (prefixWord ++ tailWord_3020889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020889).length < 2 ^ (prefixWord ++ tailWord_3020889).sum := by decide
  have hdescent : baseEnd_3020889 < baseStart_3020889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020981 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 5]
def baseStart_3020981 : Nat := 118140960795 + 3020981 * 2 ^ 59
def prefixEnd_3020981 : Nat := 4983230072969 + 3 ^ 40 * 3020981 * 2
def baseEnd_3020981 : Nat := 344714511355633362587615

theorem tailTrace_3020981 : CollatzResearch.WordTrace tailWord_3020981 prefixEnd_3020981 344714511355633362587615 := by
  unfold tailWord_3020981
  simp only [CollatzResearch.WordTrace]
  refine ⟨110184229068509254323630797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73456152712339502882420531 110184229068509254323630797)
  ·
    refine ⟨41319085900690970371361549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110184229068509254323630797 41319085900690970371361549)
    ·
      refine ⟨15494657212759113889260581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41319085900690970371361549 15494657212759113889260581)
      ·
        refine ⟨2905248227392333854236359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15494657212759113889260581 2905248227392333854236359)
        ·
          refine ⟨4357872341088500781354539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905248227392333854236359 4357872341088500781354539)
          ·
            refine ⟨6536808511632751172031809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357872341088500781354539 6536808511632751172031809)
            ·
              refine ⟨4902606383724563379023857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6536808511632751172031809 4902606383724563379023857)
              ·
                refine ⟨3676954787793422534267893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4902606383724563379023857 3676954787793422534267893)
                ·
                  refine ⟨344714511355633362587615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3676954787793422534267893 344714511355633362587615)
                  ·
                    rfl

theorem cell22_3020981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_3020981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3020981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3020981 prefixEnd_3020981 := by exact prefixLift 3020981
  have htrace : WordTrace (prefixWord ++ tailWord_3020981) baseStart_3020981 baseEnd_3020981 := by
    simpa [prefixWord, tailWord_3020981, baseEnd_3020981] using wordTrace_append hprefix tailTrace_3020981
  have hstable : (prefixWord ++ tailWord_3020981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020981).length < 2 ^ (prefixWord ++ tailWord_3020981).sum := by decide
  have hdescent : baseEnd_3020981 < baseStart_3020981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021007 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 1, 5]
def baseStart_3021007 : Nat := 118140960795 + 3021007 * 2 ^ 59
def prefixEnd_3021007 : Nat := 4983230072969 + 3 ^ 40 * 3021007 * 2
def baseEnd_3021007 : Nat := 1034152434398244686612765

theorem tailTrace_3021007 : CollatzResearch.WordTrace tailWord_3021007 prefixEnd_3021007 1034152434398244686612765 := by
  unfold tailWord_3021007
  simp only [CollatzResearch.WordTrace]
  refine ⟨110185177366415060764077275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73456784910943373842718183 110185177366415060764077275)
  ·
    refine ⟨165277766049622591146115913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110185177366415060764077275 165277766049622591146115913)
    ·
      refine ⟨123958324537216943359586935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165277766049622591146115913 123958324537216943359586935)
      ·
        refine ⟨185937486805825415039380403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123958324537216943359586935 185937486805825415039380403)
        ·
          refine ⟨278906230208738122559070605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185937486805825415039380403 278906230208738122559070605)
          ·
            refine ⟨104589836328276795959651477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278906230208738122559070605 104589836328276795959651477)
            ·
              refine ⟨4902648577887974810608663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104589836328276795959651477 4902648577887974810608663)
              ·
                refine ⟨7353972866831962215912995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4902648577887974810608663 7353972866831962215912995)
                ·
                  refine ⟨11030959300247943323869493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7353972866831962215912995 11030959300247943323869493)
                  ·
                    refine ⟨1034152434398244686612765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11030959300247943323869493 1034152434398244686612765)
                    ·
                      rfl

theorem cell22_3021007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_3021007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021007 prefixEnd_3021007 := by exact prefixLift 3021007
  have htrace : WordTrace (prefixWord ++ tailWord_3021007) baseStart_3021007 baseEnd_3021007 := by
    simpa [prefixWord, tailWord_3021007, baseEnd_3021007] using wordTrace_append hprefix tailTrace_3021007
  have hstable : (prefixWord ++ tailWord_3021007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021007).length < 2 ^ (prefixWord ++ tailWord_3021007).sum := by decide
  have hdescent : baseEnd_3021007 < baseStart_3021007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021127 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 8]
def baseStart_3021127 : Nat := 118140960795 + 3021127 * 2 ^ 59
def prefixEnd_3021127 : Nat := 4983230072969 + 3 ^ 40 * 3021127 * 2
def baseEnd_3021127 : Nat := 344731170950201457870799

theorem tailTrace_3021127 : CollatzResearch.WordTrace tailWord_3021127 prefixEnd_3021127 344731170950201457870799 := by
  unfold tailWord_3021127
  simp only [CollatzResearch.WordTrace]
  refine ⟨110189554125980321258445635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73459702750653547505630423 110189554125980321258445635)
  ·
    refine ⟨165284331188970481887668453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110189554125980321258445635 165284331188970481887668453)
    ·
      refine ⟨30990812097931965353937835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165284331188970481887668453 30990812097931965353937835)
      ·
        refine ⟨46486218146897948030906753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30990812097931965353937835 46486218146897948030906753)
        ·
          refine ⟨34864663610173461023180065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46486218146897948030906753 34864663610173461023180065)
          ·
            refine ⟨26148497707630095767385049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34864663610173461023180065 26148497707630095767385049)
            ·
              refine ⟨19611373280722571825538787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26148497707630095767385049 19611373280722571825538787)
              ·
                refine ⟨29417059921083857738308181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19611373280722571825538787 29417059921083857738308181)
                ·
                  refine ⟨344731170950201457870799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29417059921083857738308181 344731170950201457870799)
                  ·
                    rfl

theorem cell22_3021127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 8].length) (baseStart_3021127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021127 prefixEnd_3021127 := by exact prefixLift 3021127
  have htrace : WordTrace (prefixWord ++ tailWord_3021127) baseStart_3021127 baseEnd_3021127 := by
    simpa [prefixWord, tailWord_3021127, baseEnd_3021127] using wordTrace_append hprefix tailTrace_3021127
  have hstable : (prefixWord ++ tailWord_3021127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021127).length < 2 ^ (prefixWord ++ tailWord_3021127).sum := by decide
  have hdescent : baseEnd_3021127 < baseStart_3021127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021221 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_3021221 : Nat := 118140960795 + 3021221 * 2 ^ 59
def prefixEnd_3021221 : Nat := 4983230072969 + 3 ^ 40 * 3021221 * 2
def baseEnd_3021221 : Nat := 1034225690971619461762109

theorem tailTrace_3021221 : CollatzResearch.WordTrace tailWord_3021221 prefixEnd_3021221 1034225690971619461762109 := by
  unfold tailWord_3021221
  simp only [CollatzResearch.WordTrace]
  refine ⟨110192982587639775312367517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73461988391759850208245011 110192982587639775312367517)
  ·
    refine ⟨41322368470364915742137819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110192982587639775312367517 41322368470364915742137819)
    ·
      refine ⟨61983552705547373613206729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41322368470364915742137819 61983552705547373613206729)
      ·
        refine ⟨46487664529160530209905047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61983552705547373613206729 46487664529160530209905047)
        ·
          refine ⟨69731496793740795314857571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46487664529160530209905047 69731496793740795314857571)
          ·
            refine ⟨104597245190611192972286357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69731496793740795314857571 104597245190611192972286357)
            ·
              refine ⟨4902995868309899670575923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104597245190611192972286357 4902995868309899670575923)
              ·
                refine ⟨7354493802464849505863885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4902995868309899670575923 7354493802464849505863885)
                ·
                  refine ⟨2757935175924318564698957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7354493802464849505863885 2757935175924318564698957)
                  ·
                    refine ⟨1034225690971619461762109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757935175924318564698957 1034225690971619461762109)
                    ·
                      rfl

theorem cell22_3021221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_3021221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021221 prefixEnd_3021221 := by exact prefixLift 3021221
  have htrace : WordTrace (prefixWord ++ tailWord_3021221) baseStart_3021221 baseEnd_3021221 := by
    simpa [prefixWord, tailWord_3021221, baseEnd_3021221] using wordTrace_append hprefix tailTrace_3021221
  have hstable : (prefixWord ++ tailWord_3021221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021221).length < 2 ^ (prefixWord ++ tailWord_3021221).sum := by decide
  have hdescent : baseEnd_3021221 < baseStart_3021221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021255 : List Nat := [1, 1, 4, 1, 1, 6, 1, 3, 1, 3]
def baseStart_3021255 : Nat := 118140960795 + 3021255 * 2 ^ 59
def prefixEnd_3021255 : Nat := 4983230072969 + 3 ^ 40 * 3021255 * 2
def baseEnd_3021255 : Nat := 1034237329866454706412005

theorem tailTrace_3021255 : CollatzResearch.WordTrace tailWord_3021255 prefixEnd_3021255 1034237329866454706412005 := by
  unfold tailWord_3021255
  simp only [CollatzResearch.WordTrace]
  refine ⟨110194222669516599119105219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73462815113011066079403479 110194222669516599119105219)
  ·
    refine ⟨165291334004274898678657829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110194222669516599119105219 165291334004274898678657829)
    ·
      refine ⟨30992125125801543502248343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165291334004274898678657829 30992125125801543502248343)
      ·
        refine ⟨46488187688702315253372515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30992125125801543502248343 46488187688702315253372515)
        ·
          refine ⟨69732281533053472880058773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46488187688702315253372515 69732281533053472880058773)
          ·
            refine ⟨3268700696861881541252755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69732281533053472880058773 3268700696861881541252755)
            ·
              refine ⟨4903051045292822311879133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268700696861881541252755 4903051045292822311879133)
              ·
                refine ⟨1838644141984808366954675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4903051045292822311879133 1838644141984808366954675)
                ·
                  refine ⟨2757966212977212550432013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838644141984808366954675 2757966212977212550432013)
                  ·
                    refine ⟨1034237329866454706412005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757966212977212550432013 1034237329866454706412005)
                    ·
                      rfl

theorem cell22_3021255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_3021255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021255 prefixEnd_3021255 := by exact prefixLift 3021255
  have htrace : WordTrace (prefixWord ++ tailWord_3021255) baseStart_3021255 baseEnd_3021255 := by
    simpa [prefixWord, tailWord_3021255, baseEnd_3021255] using wordTrace_append hprefix tailTrace_3021255
  have hstable : (prefixWord ++ tailWord_3021255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021255).length < 2 ^ (prefixWord ++ tailWord_3021255).sum := by decide
  have hdescent : baseEnd_3021255 < baseStart_3021255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021285 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 5]
def baseStart_3021285 : Nat := 118140960795 + 3021285 * 2 ^ 59
def prefixEnd_3021285 : Nat := 4983230072969 + 3 ^ 40 * 3021285 * 2
def baseEnd_3021285 : Nat := 344749199826514876053971

theorem tailTrace_3021285 : CollatzResearch.WordTrace tailWord_3021285 prefixEnd_3021285 344749199826514876053971 := by
  unfold tailWord_3021285
  simp only [CollatzResearch.WordTrace]
  refine ⟨110195316859407914242697309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73463544572938609495131539 110195316859407914242697309)
  ·
    refine ⟨41323243822277967841011491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110195316859407914242697309 41323243822277967841011491)
    ·
      refine ⟨61984865733416951761517237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41323243822277967841011491 61984865733416951761517237)
      ·
        refine ⟨5811081162507839227642241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61984865733416951761517237 5811081162507839227642241)
        ·
          refine ⟨4358310871880879420731681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5811081162507839227642241 4358310871880879420731681)
          ·
            refine ⟨3268733153910659565548761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358310871880879420731681 3268733153910659565548761)
            ·
              refine ⟨2451549865432994674161571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3268733153910659565548761 2451549865432994674161571)
              ·
                refine ⟨3677324798149492011242357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451549865432994674161571 3677324798149492011242357)
                ·
                  refine ⟨344749199826514876053971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3677324798149492011242357 344749199826514876053971)
                  ·
                    rfl

theorem cell22_3021285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_3021285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021285 prefixEnd_3021285 := by exact prefixLift 3021285
  have htrace : WordTrace (prefixWord ++ tailWord_3021285) baseStart_3021285 baseEnd_3021285 := by
    simpa [prefixWord, tailWord_3021285, baseEnd_3021285] using wordTrace_append hprefix tailTrace_3021285
  have hstable : (prefixWord ++ tailWord_3021285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021285).length < 2 ^ (prefixWord ++ tailWord_3021285).sum := by decide
  have hdescent : baseEnd_3021285 < baseStart_3021285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021298 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3021298 : Nat := 118140960795 + 3021298 * 2 ^ 59
def prefixEnd_3021298 : Nat := 4983230072969 + 3 ^ 40 * 3021298 * 2
def baseEnd_3021298 : Nat := 1034252049645216927586873

theorem tailTrace_3021298 : CollatzResearch.WordTrace tailWord_3021298 prefixEnd_3021298 1034252049645216927586873 := by
  unfold tailWord_3021298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27548947752090204365730137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73463860672240544975280365 27548947752090204365730137)
  ·
    refine ⟨20661710814067653274297603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27548947752090204365730137 20661710814067653274297603)
    ·
      refine ⟨30992566221101479911446405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20661710814067653274297603 30992566221101479911446405)
      ·
        refine ⟨5811106166456527483396201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30992566221101479911446405 5811106166456527483396201)
        ·
          refine ⟨4358329624842395612547151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5811106166456527483396201 4358329624842395612547151)
          ·
            refine ⟨6537494437263593418820727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358329624842395612547151 6537494437263593418820727)
            ·
              refine ⟨9806241655895390128231091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6537494437263593418820727 9806241655895390128231091)
              ·
                refine ⟨14709362483843085192346637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806241655895390128231091 14709362483843085192346637)
                ·
                  refine ⟨5516010931441156947129989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14709362483843085192346637 5516010931441156947129989)
                  ·
                    refine ⟨1034252049645216927586873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5516010931441156947129989 1034252049645216927586873)
                    ·
                      rfl

theorem cell22_3021298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3021298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021298 prefixEnd_3021298 := by exact prefixLift 3021298
  have htrace : WordTrace (prefixWord ++ tailWord_3021298) baseStart_3021298 baseEnd_3021298 := by
    simpa [prefixWord, tailWord_3021298, baseEnd_3021298] using wordTrace_append hprefix tailTrace_3021298
  have hstable : (prefixWord ++ tailWord_3021298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021298).length < 2 ^ (prefixWord ++ tailWord_3021298).sum := by decide
  have hdescent : baseEnd_3021298 < baseStart_3021298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021324 : List Nat := [2, 2, 1, 2, 4, 11]
def baseStart_3021324 : Nat := 118140960795 + 3021324 * 2 ^ 59
def prefixEnd_3021324 : Nat := 4983230072969 + 3 ^ 40 * 3021324 * 2
def baseEnd_3021324 : Nat := 12768653703414339832553

theorem tailTrace_3021324 : CollatzResearch.WordTrace tailWord_3021324 prefixEnd_3021324 12768653703414339832553 := by
  unfold tailWord_3021324
  simp only [CollatzResearch.WordTrace]
  refine ⟨55098369653133311951683513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73464492870844415935578017 55098369653133311951683513)
  ·
    refine ⟨41323777239849983963762635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55098369653133311951683513 41323777239849983963762635)
    ·
      refine ⟨61985665859774975945643953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41323777239849983963762635 61985665859774975945643953)
      ·
        refine ⟨46489249394831231959232965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61985665859774975945643953 46489249394831231959232965)
        ·
          refine ⟨8716734261530855992356181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46489249394831231959232965 8716734261530855992356181)
          ·
            refine ⟨12768653703414339832553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8716734261530855992356181 12768653703414339832553)
            ·
              rfl

theorem cell22_3021324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 11].length) (baseStart_3021324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021324 prefixEnd_3021324 := by exact prefixLift 3021324
  have htrace : WordTrace (prefixWord ++ tailWord_3021324) baseStart_3021324 baseEnd_3021324 := by
    simpa [prefixWord, tailWord_3021324, baseEnd_3021324] using wordTrace_append hprefix tailTrace_3021324
  have hstable : (prefixWord ++ tailWord_3021324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021324).length < 2 ^ (prefixWord ++ tailWord_3021324).sum := by decide
  have hdescent : baseEnd_3021324 < baseStart_3021324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021341 : List Nat := [1, 4, 2, 2, 1, 2, 3, 7]
def baseStart_3021341 : Nat := 118140960795 + 3021341 * 2 ^ 59
def prefixEnd_3021341 : Nat := 4983230072969 + 3 ^ 40 * 3021341 * 2
def baseEnd_3021341 : Nat := 114918529935997683195749

theorem tailTrace_3021341 : CollatzResearch.WordTrace tailWord_3021341 prefixEnd_3021341 114918529935997683195749 := by
  unfold tailWord_3021341
  simp only [CollatzResearch.WordTrace]
  refine ⟨110197359347205035806735877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73464906231470023871157251 110197359347205035806735877)
  ·
    refine ⟨20662004877600944213762977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110197359347205035806735877 20662004877600944213762977)
    ·
      refine ⟨15496503658200708160322233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20662004877600944213762977 15496503658200708160322233)
      ·
        refine ⟨11622377743650531120241675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15496503658200708160322233 11622377743650531120241675)
        ·
          refine ⟨17433566615475796680362513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11622377743650531120241675 17433566615475796680362513)
          ·
            refine ⟨13075174961606847510271885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17433566615475796680362513 13075174961606847510271885)
            ·
              refine ⟨4903190610602567816351957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13075174961606847510271885 4903190610602567816351957)
              ·
                refine ⟨114918529935997683195749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4903190610602567816351957 114918529935997683195749)
                ·
                  rfl

theorem cell22_3021341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 7].length) (baseStart_3021341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021341 prefixEnd_3021341 := by exact prefixLift 3021341
  have htrace : WordTrace (prefixWord ++ tailWord_3021341) baseStart_3021341 baseEnd_3021341 := by
    simpa [prefixWord, tailWord_3021341, baseEnd_3021341] using wordTrace_append hprefix tailTrace_3021341
  have hstable : (prefixWord ++ tailWord_3021341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021341).length < 2 ^ (prefixWord ++ tailWord_3021341).sum := by decide
  have hdescent : baseEnd_3021341 < baseStart_3021341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021386 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_3021386 : Nat := 118140960795 + 3021386 * 2 ^ 59
def prefixEnd_3021386 : Nat := 4983230072969 + 3 ^ 40 * 3021386 * 2
def baseEnd_3021386 : Nat := 344760724614538010462201

theorem tailTrace_3021386 : CollatzResearch.WordTrace tailWord_3021386 prefixEnd_3021386 344760724614538010462201 := by
  unfold tailWord_3021386
  simp only [CollatzResearch.WordTrace]
  refine ⟨27549750158010502123031003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73466000421361338994749341 27549750158010502123031003)
  ·
    refine ⟨41324625237015753184546505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27549750158010502123031003 41324625237015753184546505)
    ·
      refine ⟨30993468927761814888409879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41324625237015753184546505 30993468927761814888409879)
      ·
        refine ⟨46490203391642722332614819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30993468927761814888409879 46490203391642722332614819)
        ·
          refine ⟨69735305087464083498922229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46490203391642722332614819 69735305087464083498922229)
          ·
            refine ⟨6537684851949757828023959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69735305087464083498922229 6537684851949757828023959)
            ·
              refine ⟨9806527277924636742035939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6537684851949757828023959 9806527277924636742035939)
              ·
                refine ⟨14709790916886955113053909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806527277924636742035939 14709790916886955113053909)
                ·
                  refine ⟨344760724614538010462201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14709790916886955113053909 344760724614538010462201)
                  ·
                    rfl

theorem cell22_3021386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_3021386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021386 prefixEnd_3021386 := by exact prefixLift 3021386
  have htrace : WordTrace (prefixWord ++ tailWord_3021386) baseStart_3021386 baseEnd_3021386 := by
    simpa [prefixWord, tailWord_3021386, baseEnd_3021386] using wordTrace_append hprefix tailTrace_3021386
  have hstable : (prefixWord ++ tailWord_3021386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021386).length < 2 ^ (prefixWord ++ tailWord_3021386).sum := by decide
  have hdescent : baseEnd_3021386 < baseStart_3021386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021390 : List Nat := [4, 1, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_3021390 : Nat := 118140960795 + 3021390 * 2 ^ 59
def prefixEnd_3021390 : Nat := 4983230072969 + 3 ^ 40 * 3021390 * 2
def baseEnd_3021390 : Nat := 1034283543125359354286591

theorem tailTrace_3021390 : CollatzResearch.WordTrace tailWord_3021390 prefixEnd_3021390 1034283543125359354286591 := by
  unfold tailWord_3021390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774893315503439646908703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73466097682685011450179749 13774893315503439646908703)
  ·
    refine ⟨20662339973255159470363055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13774893315503439646908703 20662339973255159470363055)
    ·
      refine ⟨30993509959882739205544583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20662339973255159470363055 30993509959882739205544583)
      ·
        refine ⟨46490264939824108808316875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30993509959882739205544583 46490264939824108808316875)
        ·
          refine ⟨69735397409736163212475313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46490264939824108808316875 69735397409736163212475313)
          ·
            refine ⟨52301548057302122409356485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69735397409736163212475313 52301548057302122409356485)
            ·
              refine ⟨9806540260744147951754341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52301548057302122409356485 9806540260744147951754341)
              ·
                refine ⟨1838726298889527740953939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9806540260744147951754341 1838726298889527740953939)
                ·
                  refine ⟨2758089448334291611430909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838726298889527740953939 2758089448334291611430909)
                  ·
                    refine ⟨1034283543125359354286591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2758089448334291611430909 1034283543125359354286591)
                    ·
                      rfl

theorem cell22_3021390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_3021390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021390 prefixEnd_3021390 := by exact prefixLift 3021390
  have htrace : WordTrace (prefixWord ++ tailWord_3021390) baseStart_3021390 baseEnd_3021390 := by
    simpa [prefixWord, tailWord_3021390, baseEnd_3021390] using wordTrace_append hprefix tailTrace_3021390
  have hstable : (prefixWord ++ tailWord_3021390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021390).length < 2 ^ (prefixWord ++ tailWord_3021390).sum := by decide
  have hdescent : baseEnd_3021390 < baseStart_3021390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021424 : List Nat := [2, 1, 1, 1, 8, 1, 1, 3, 1, 3]
def baseStart_3021424 : Nat := 118140960795 + 3021424 * 2 ^ 59
def prefixEnd_3021424 : Nat := 4983230072969 + 3 ^ 40 * 3021424 * 2
def baseEnd_3021424 : Nat := 1034295182020194598936487

theorem tailTrace_3021424 : CollatzResearch.WordTrace tailWord_3021424 prefixEnd_3021424 1034295182020194598936487 := by
  unfold tailWord_3021424
  simp only [CollatzResearch.WordTrace]
  refine ⟨55100193302952170491003663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73466924403936227321338217 55100193302952170491003663)
  ·
    refine ⟨82650289954428255736505495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55100193302952170491003663 82650289954428255736505495)
    ·
      refine ⟨123975434931642383604758243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82650289954428255736505495 123975434931642383604758243)
      ·
        refine ⟨185963152397463575407137365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123975434931642383604758243 185963152397463575407137365)
        ·
          refine ⟨2179255692157776274302391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 185963152397463575407137365 2179255692157776274302391)
          ·
            refine ⟨3268883538236664411453587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179255692157776274302391 3268883538236664411453587)
            ·
              refine ⟨4903325307354996617180381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268883538236664411453587 4903325307354996617180381)
              ·
                refine ⟨1838746990258123731442643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4903325307354996617180381 1838746990258123731442643)
                ·
                  refine ⟨2758120485387185597163965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838746990258123731442643 2758120485387185597163965)
                  ·
                    refine ⟨1034295182020194598936487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2758120485387185597163965 1034295182020194598936487)
                    ·
                      rfl

theorem cell22_3021424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 3].length) (baseStart_3021424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021424 prefixEnd_3021424 := by exact prefixLift 3021424
  have htrace : WordTrace (prefixWord ++ tailWord_3021424) baseStart_3021424 baseEnd_3021424 := by
    simpa [prefixWord, tailWord_3021424, baseEnd_3021424] using wordTrace_append hprefix tailTrace_3021424
  have hstable : (prefixWord ++ tailWord_3021424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021424).length < 2 ^ (prefixWord ++ tailWord_3021424).sum := by decide
  have hdescent : baseEnd_3021424 < baseStart_3021424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021433 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_3021433 : Nat := 118140960795 + 3021433 * 2 ^ 59
def prefixEnd_3021433 : Nat := 4983230072969 + 3 ^ 40 * 3021433 * 2
def baseEnd_3021433 : Nat := 1034298262904121575461459

theorem tailTrace_3021433 : CollatzResearch.WordTrace tailWord_3021433 prefixEnd_3021433 1034298262904121575461459 := by
  unfold tailWord_3021433
  simp only [CollatzResearch.WordTrace]
  refine ⟨110200714862871735519084953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73467143241914490346056635 110200714862871735519084953)
  ·
    refine ⟨82650536147153801639313715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110200714862871735519084953 82650536147153801639313715)
    ·
      refine ⟨123975804220730702458970573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82650536147153801639313715 123975804220730702458970573)
      ·
        refine ⟨46490926582774013422113965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123975804220730702458970573 46490926582774013422113965)
        ·
          refine ⟨17434097468540255033292737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46490926582774013422113965 17434097468540255033292737)
          ·
            refine ⟨13075573101405191274969553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17434097468540255033292737 13075573101405191274969553)
            ·
              refine ⟨9806679826053893456227165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13075573101405191274969553 9806679826053893456227165)
              ·
                refine ⟨3677504934770210046085187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9806679826053893456227165 3677504934770210046085187)
                ·
                  refine ⟨5516257402155315069127781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677504934770210046085187 5516257402155315069127781)
                  ·
                    refine ⟨1034298262904121575461459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5516257402155315069127781 1034298262904121575461459)
                    ·
                      rfl

theorem cell22_3021433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_3021433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021433 prefixEnd_3021433 := by exact prefixLift 3021433
  have htrace : WordTrace (prefixWord ++ tailWord_3021433) baseStart_3021433 baseEnd_3021433 := by
    simpa [prefixWord, tailWord_3021433, baseEnd_3021433] using wordTrace_append hprefix tailTrace_3021433
  have hstable : (prefixWord ++ tailWord_3021433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021433).length < 2 ^ (prefixWord ++ tailWord_3021433).sum := by decide
  have hdescent : baseEnd_3021433 < baseStart_3021433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021476 : List Nat := [2, 3, 1, 2, 2, 1, 1, 10]
def baseStart_3021476 : Nat := 118140960795 + 3021476 * 2 ^ 59
def prefixEnd_3021476 : Nat := 4983230072969 + 3 ^ 40 * 3021476 * 2
def baseEnd_3021476 : Nat := 114923664742542644070703

theorem tailTrace_3021476 : CollatzResearch.WordTrace tailWord_3021476 prefixEnd_3021476 114923664742542644070703 := by
  unfold tailWord_3021476
  simp only [CollatzResearch.WordTrace]
  refine ⟨55101141600857976931450141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73468188801143969241933521 55101141600857976931450141)
  ·
    refine ⟨20662928100321741349293803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55101141600857976931450141 20662928100321741349293803)
    ·
      refine ⟨30994392150482612023940705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20662928100321741349293803 30994392150482612023940705)
      ·
        refine ⟨23245794112861959017955529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30994392150482612023940705 23245794112861959017955529)
        ·
          refine ⟨17434345584646469263466647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23245794112861959017955529 17434345584646469263466647)
          ·
            refine ⟨26151518376969703895199971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17434345584646469263466647 26151518376969703895199971)
            ·
              refine ⟨39227277565454555842799957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26151518376969703895199971 39227277565454555842799957)
              ·
                refine ⟨114923664742542644070703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39227277565454555842799957 114923664742542644070703)
                ·
                  rfl

theorem cell22_3021476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 10].length) (baseStart_3021476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021476 prefixEnd_3021476 := by exact prefixLift 3021476
  have htrace : WordTrace (prefixWord ++ tailWord_3021476) baseStart_3021476 baseEnd_3021476 := by
    simpa [prefixWord, tailWord_3021476, baseEnd_3021476] using wordTrace_append hprefix tailTrace_3021476
  have hstable : (prefixWord ++ tailWord_3021476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021476).length < 2 ^ (prefixWord ++ tailWord_3021476).sum := by decide
  have hdescent : baseEnd_3021476 < baseStart_3021476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021536 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_3021536 : Nat := 118140960795 + 3021536 * 2 ^ 59
def prefixEnd_3021536 : Nat := 4983230072969 + 3 ^ 40 * 3021536 * 2
def baseEnd_3021536 : Nat := 1034333521909063640136143

theorem tailTrace_3021536 : CollatzResearch.WordTrace tailWord_3021536 prefixEnd_3021536 1034333521909063640136143 := by
  unfold tailWord_3021536
  simp only [CollatzResearch.WordTrace]
  refine ⟨55102235790749292055042231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73469647720999056073389641 55102235790749292055042231)
  ·
    refine ⟨82653353686123938082563347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55102235790749292055042231 82653353686123938082563347)
    ·
      refine ⟨123980030529185907123845021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82653353686123938082563347 123980030529185907123845021)
      ·
        refine ⟨46492511448444715171441883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123980030529185907123845021 46492511448444715171441883)
        ·
          refine ⟨69738767172667072757162825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46492511448444715171441883 69738767172667072757162825)
          ·
            refine ⟨52304075379500304567872119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69738767172667072757162825 52304075379500304567872119)
            ·
              refine ⟨78456113069250456851808179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52304075379500304567872119 78456113069250456851808179)
              ·
                refine ⟨117684169603875685277712269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78456113069250456851808179 117684169603875685277712269)
                ·
                  refine ⟨44131563601453381979142101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117684169603875685277712269 44131563601453381979142101)
                  ·
                    refine ⟨1034333521909063640136143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44131563601453381979142101 1034333521909063640136143)
                    ·
                      rfl

theorem cell22_3021536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_3021536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021536 prefixEnd_3021536 := by exact prefixLift 3021536
  have htrace : WordTrace (prefixWord ++ tailWord_3021536) baseStart_3021536 baseEnd_3021536 := by
    simpa [prefixWord, tailWord_3021536, baseEnd_3021536] using wordTrace_append hprefix tailTrace_3021536
  have hstable : (prefixWord ++ tailWord_3021536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021536).length < 2 ^ (prefixWord ++ tailWord_3021536).sum := by decide
  have hdescent : baseEnd_3021536 < baseStart_3021536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021570 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3021570 : Nat := 118140960795 + 3021570 * 2 ^ 59
def prefixEnd_3021570 : Nat := 4983230072969 + 3 ^ 40 * 3021570 * 2
def baseEnd_3021570 : Nat := 1034345160803898884786039

theorem tailTrace_3021570 : CollatzResearch.WordTrace tailWord_3021570 prefixEnd_3021570 1034345160803898884786039 := by
  unfold tailWord_3021570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27551427915843851979205541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73470474442250271944548109 27551427915843851979205541)
  ·
    refine ⟨5165892734220722246101039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27551427915843851979205541 5165892734220722246101039)
    ·
      refine ⟨7748839101331083369151559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165892734220722246101039 7748839101331083369151559)
      ·
        refine ⟨11623258651996625053727339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7748839101331083369151559 11623258651996625053727339)
        ·
          refine ⟨17434887977994937580591009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11623258651996625053727339 17434887977994937580591009)
          ·
            refine ⟨13076165983496203185443257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17434887977994937580591009 13076165983496203185443257)
            ·
              refine ⟨9807124487622152389082443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13076165983496203185443257 9807124487622152389082443)
              ·
                refine ⟨14710686731433228583623665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9807124487622152389082443 14710686731433228583623665)
                ·
                  refine ⟨11033015048574921437717749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14710686731433228583623665 11033015048574921437717749)
                  ·
                    refine ⟨1034345160803898884786039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11033015048574921437717749 1034345160803898884786039)
                    ·
                      rfl

theorem cell22_3021570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3021570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021570 prefixEnd_3021570 := by exact prefixLift 3021570
  have htrace : WordTrace (prefixWord ++ tailWord_3021570) baseStart_3021570 baseEnd_3021570 := by
    simpa [prefixWord, tailWord_3021570, baseEnd_3021570] using wordTrace_append hprefix tailTrace_3021570
  have hstable : (prefixWord ++ tailWord_3021570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021570).length < 2 ^ (prefixWord ++ tailWord_3021570).sum := by decide
  have hdescent : baseEnd_3021570 < baseStart_3021570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021617 : List Nat := [1, 2, 2, 3, 2, 1, 5, 2, 4]
def baseStart_3021617 : Nat := 118140960795 + 3021617 * 2 ^ 59
def prefixEnd_3021617 : Nat := 4983230072969 + 3 ^ 40 * 3021617 * 2
def baseEnd_3021617 : Nat := 344787083288135476286965

theorem tailTrace_3021617 : CollatzResearch.WordTrace tailWord_3021617 prefixEnd_3021617 344787083288135476286965 := by
  unfold tailWord_3021617
  simp only [CollatzResearch.WordTrace]
  refine ⟨110207425894205134943783105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73471617262803423295855403 110207425894205134943783105)
  ·
    refine ⟨82655569420653851207837329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110207425894205134943783105 82655569420653851207837329)
    ·
      refine ⟨61991677065490388405877997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82655569420653851207837329 61991677065490388405877997)
      ·
        refine ⟨23246878899558895652204249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61991677065490388405877997 23246878899558895652204249)
        ·
          refine ⟨17435159174669171739153187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23246878899558895652204249 17435159174669171739153187)
          ·
            refine ⟨26152738762003757608729781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17435159174669171739153187 26152738762003757608729781)
            ·
              refine ⟨2451819258937852275818417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26152738762003757608729781 2451819258937852275818417)
              ·
                refine ⟨1838864444203389206863813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451819258937852275818417 1838864444203389206863813)
                ·
                  refine ⟨344787083288135476286965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1838864444203389206863813 344787083288135476286965)
                  ·
                    rfl

theorem cell22_3021617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 4].length) (baseStart_3021617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021617 prefixEnd_3021617 := by exact prefixLift 3021617
  have htrace : WordTrace (prefixWord ++ tailWord_3021617) baseStart_3021617 baseEnd_3021617 := by
    simpa [prefixWord, tailWord_3021617, baseEnd_3021617] using wordTrace_append hprefix tailTrace_3021617
  have hstable : (prefixWord ++ tailWord_3021617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021617).length < 2 ^ (prefixWord ++ tailWord_3021617).sum := by decide
  have hdescent : baseEnd_3021617 < baseStart_3021617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021636 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3021636 : Nat := 118140960795 + 3021636 * 2 ^ 59
def prefixEnd_3021636 : Nat := 4983230072969 + 3 ^ 40 * 3021636 * 2
def baseEnd_3021636 : Nat := 1034367753952696712635837

theorem tailTrace_3021636 : CollatzResearch.WordTrace tailWord_3021636 prefixEnd_3021636 1034367753952696712635837 := by
  unfold tailWord_3021636
  simp only [CollatzResearch.WordTrace]
  refine ⟨55104059440568150594362381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73472079254090867459149841 55104059440568150594362381)
  ·
    refine ⟨20664022290213056472885893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55104059440568150594362381 20664022290213056472885893)
    ·
      refine ⟨3874504179414948088666105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20664022290213056472885893 3874504179414948088666105)
      ·
        refine ⟨2905878134561211066499579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3874504179414948088666105 2905878134561211066499579)
        ·
          refine ⟨4358817201841816599749369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905878134561211066499579 4358817201841816599749369)
          ·
            refine ⟨3269112901381362449812027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358817201841816599749369 3269112901381362449812027)
            ·
              refine ⟨4903669352072043674718041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269112901381362449812027 4903669352072043674718041)
              ·
                refine ⟨3677752014054032756038531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4903669352072043674718041 3677752014054032756038531)
                ·
                  refine ⟨5516628021081049134057797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677752014054032756038531 5516628021081049134057797)
                  ·
                    refine ⟨1034367753952696712635837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5516628021081049134057797 1034367753952696712635837)
                    ·
                      rfl

theorem cell22_3021636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3021636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021636 prefixEnd_3021636 := by exact prefixLift 3021636
  have htrace : WordTrace (prefixWord ++ tailWord_3021636) baseStart_3021636 baseEnd_3021636 := by
    simpa [prefixWord, tailWord_3021636, baseEnd_3021636] using wordTrace_append hprefix tailTrace_3021636
  have hstable : (prefixWord ++ tailWord_3021636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021636).length < 2 ^ (prefixWord ++ tailWord_3021636).sum := by decide
  have hdescent : baseEnd_3021636 < baseStart_3021636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021698 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3021698 : Nat := 118140960795 + 3021698 * 2 ^ 59
def prefixEnd_3021698 : Nat := 4983230072969 + 3 ^ 40 * 3021698 * 2
def baseEnd_3021698 : Nat := 1034388977819749217585647

theorem tailTrace_3021698 : CollatzResearch.WordTrace tailWord_3021698 prefixEnd_3021698 1034388977819749217585647 := by
  unfold tailWord_3021698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552595051727921444370437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73473586804607790518321165 27552595051727921444370437)
  ·
    refine ⟨5166111572198985270819457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27552595051727921444370437 5166111572198985270819457)
    ·
      refine ⟨3874583679149238953114593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5166111572198985270819457 3874583679149238953114593)
      ·
        refine ⟨2905937759361929214835945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3874583679149238953114593 2905937759361929214835945)
        ·
          refine ⟨2179453319521446911126959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2905937759361929214835945 2179453319521446911126959)
          ·
            refine ⟨3269179979282170366690439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179453319521446911126959 3269179979282170366690439)
            ·
              refine ⟨4903769968923255550035659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269179979282170366690439 4903769968923255550035659)
              ·
                refine ⟨7355654953384883325053489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903769968923255550035659 7355654953384883325053489)
                ·
                  refine ⟨5516741215038662493790117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7355654953384883325053489 5516741215038662493790117)
                  ·
                    refine ⟨1034388977819749217585647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5516741215038662493790117 1034388977819749217585647)
                    ·
                      rfl

theorem cell22_3021698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3021698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021698 prefixEnd_3021698 := by exact prefixLift 3021698
  have htrace : WordTrace (prefixWord ++ tailWord_3021698) baseStart_3021698 baseEnd_3021698 := by
    simpa [prefixWord, tailWord_3021698, baseEnd_3021698] using wordTrace_append hprefix tailTrace_3021698
  have hstable : (prefixWord ++ tailWord_3021698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021698).length < 2 ^ (prefixWord ++ tailWord_3021698).sum := by decide
  have hdescent : baseEnd_3021698 < baseStart_3021698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021724 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 5]
def baseStart_3021724 : Nat := 118140960795 + 3021724 * 2 ^ 59
def prefixEnd_3021724 : Nat := 4983230072969 + 3 ^ 40 * 3021724 * 2
def baseEnd_3021724 : Nat := 344799292717031272145189

theorem tailTrace_3021724 : CollatzResearch.WordTrace tailWord_3021724 prefixEnd_3021724 344799292717031272145189 := by
  unfold tailWord_3021724
  simp only [CollatzResearch.WordTrace]
  refine ⟨55105664252408746108964113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73474219003211661478618817 55105664252408746108964113)
  ·
    refine ⟨41329248189306559581723085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55105664252408746108964113 41329248189306559581723085)
    ·
      refine ⟨15498468070989959843146157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41329248189306559581723085 15498468070989959843146157)
      ·
        refine ⟨5811925526621234941179809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15498468070989959843146157 5811925526621234941179809)
        ·
          refine ⟨4358944144965926205884857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5811925526621234941179809 4358944144965926205884857)
          ·
            refine ⟨3269208108724444654413643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358944144965926205884857 3269208108724444654413643)
            ·
              refine ⟨4903812163086666981620465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269208108724444654413643 4903812163086666981620465)
              ·
                refine ⟨3677859122315000236215349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4903812163086666981620465 3677859122315000236215349)
                ·
                  refine ⟨344799292717031272145189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3677859122315000236215349 344799292717031272145189)
                  ·
                    rfl

theorem cell22_3021724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_3021724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021724 prefixEnd_3021724 := by exact prefixLift 3021724
  have htrace : WordTrace (prefixWord ++ tailWord_3021724) baseStart_3021724 baseEnd_3021724 := by
    simpa [prefixWord, tailWord_3021724, baseEnd_3021724] using wordTrace_append hprefix tailTrace_3021724
  have hstable : (prefixWord ++ tailWord_3021724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021724).length < 2 ^ (prefixWord ++ tailWord_3021724).sum := by decide
  have hdescent : baseEnd_3021724 < baseStart_3021724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021733 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_3021733 : Nat := 118140960795 + 3021733 * 2 ^ 59
def prefixEnd_3021733 : Nat := 4983230072969 + 3 ^ 40 * 3021733 * 2
def baseEnd_3021733 : Nat := 1034400959035020792960539

theorem tailTrace_3021733 : CollatzResearch.WordTrace tailWord_3021733 prefixEnd_3021733 1034400959035020792960539 := by
  unfold tailWord_3021733
  simp only [CollatzResearch.WordTrace]
  refine ⟨110211656761784886755005853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73474437841189924503337235 110211656761784886755005853)
  ·
    refine ⟨41329371285669332533127195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110211656761784886755005853 41329371285669332533127195)
    ·
      refine ⟨61994056928503998799690793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41329371285669332533127195 61994056928503998799690793)
      ·
        refine ⟨46495542696377999099768095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61994056928503998799690793 46495542696377999099768095)
        ·
          refine ⟨69743314044566998649652143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46495542696377999099768095 69743314044566998649652143)
          ·
            refine ⟨104614971066850497974478215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69743314044566998649652143 104614971066850497974478215)
            ·
              refine ⟨156922456600275746961717323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104614971066850497974478215 156922456600275746961717323)
              ·
                refine ⟨235383684900413620442575985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156922456600275746961717323 235383684900413620442575985)
                ·
                  refine ⟨176537763675310215331931989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235383684900413620442575985 176537763675310215331931989)
                  ·
                    refine ⟨1034400959035020792960539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176537763675310215331931989 1034400959035020792960539)
                    ·
                      rfl

theorem cell22_3021733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_3021733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021733 prefixEnd_3021733 := by exact prefixLift 3021733
  have htrace : WordTrace (prefixWord ++ tailWord_3021733) baseStart_3021733 baseEnd_3021733 := by
    simpa [prefixWord, tailWord_3021733, baseEnd_3021733] using wordTrace_append hprefix tailTrace_3021733
  have hstable : (prefixWord ++ tailWord_3021733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021733).length < 2 ^ (prefixWord ++ tailWord_3021733).sum := by decide
  have hdescent : baseEnd_3021733 < baseStart_3021733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021741 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3021741 : Nat := 118140960795 + 3021741 * 2 ^ 59
def prefixEnd_3021741 : Nat := 4983230072969 + 3 ^ 40 * 3021741 * 2
def baseEnd_3021741 : Nat := 344801232532837146253505

theorem tailTrace_3021741 : CollatzResearch.WordTrace tailWord_3021741 prefixEnd_3021741 344801232532837146253505 := by
  unfold tailWord_3021741
  simp only [CollatzResearch.WordTrace]
  refine ⟨110211948545755904121297077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73474632363837269414198051 110211948545755904121297077)
  ·
    refine ⟨10332370176164616011371601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110211948545755904121297077 10332370176164616011371601)
    ·
      refine ⟨7749277632123462008528701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10332370176164616011371601 7749277632123462008528701)
      ·
        refine ⟨2905979112046298253198263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7749277632123462008528701 2905979112046298253198263)
        ·
          refine ⟨4358968668069447379797395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905979112046298253198263 4358968668069447379797395)
          ·
            refine ⟨6538453002104171069696093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358968668069447379797395 6538453002104171069696093)
            ·
              refine ⟨2451919875789064151136035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6538453002104171069696093 2451919875789064151136035)
              ·
                refine ⟨3677879813683596226704053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451919875789064151136035 3677879813683596226704053)
                ·
                  refine ⟨344801232532837146253505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3677879813683596226704053 344801232532837146253505)
                  ·
                    rfl

theorem cell22_3021741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3021741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021741 prefixEnd_3021741 := by exact prefixLift 3021741
  have htrace : WordTrace (prefixWord ++ tailWord_3021741) baseStart_3021741 baseEnd_3021741 := by
    simpa [prefixWord, tailWord_3021741, baseEnd_3021741] using wordTrace_append hprefix tailTrace_3021741
  have hstable : (prefixWord ++ tailWord_3021741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021741).length < 2 ^ (prefixWord ++ tailWord_3021741).sum := by decide
  have hdescent : baseEnd_3021741 < baseStart_3021741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021763 : List Nat := [1, 1, 1, 3, 1, 1, 2, 12]
def baseStart_3021763 : Nat := 118140960795 + 3021763 * 2 ^ 59
def prefixEnd_3021763 : Nat := 4983230072969 + 3 ^ 40 * 3021763 * 2
def baseEnd_3021763 : Nat := 114934580960901190523383

theorem tailTrace_3021763 : CollatzResearch.WordTrace tailWord_3021763 prefixEnd_3021763 114934580960901190523383 := by
  unfold tailWord_3021763
  simp only [CollatzResearch.WordTrace]
  refine ⟨110212750951676201878597943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73475167301117467919065295 110212750951676201878597943)
  ·
    refine ⟨165319126427514302817896915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110212750951676201878597943 165319126427514302817896915)
    ·
      refine ⟨247978689641271454226845373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165319126427514302817896915 247978689641271454226845373)
      ·
        refine ⟨92992008615476795335067015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247978689641271454226845373 92992008615476795335067015)
        ·
          refine ⟨139488012923215193002600523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92992008615476795335067015 139488012923215193002600523)
          ·
            refine ⟨209232019384822789503900785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139488012923215193002600523 209232019384822789503900785)
            ·
              refine ⟨156924014538617092127925589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209232019384822789503900785 156924014538617092127925589)
              ·
                refine ⟨114934580960901190523383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 156924014538617092127925589 114934580960901190523383)
                ·
                  rfl

theorem cell22_3021763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 12].length) (baseStart_3021763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021763 prefixEnd_3021763 := by exact prefixLift 3021763
  have htrace : WordTrace (prefixWord ++ tailWord_3021763) baseStart_3021763 baseEnd_3021763 := by
    simpa [prefixWord, tailWord_3021763, baseEnd_3021763] using wordTrace_append hprefix tailTrace_3021763
  have hstable : (prefixWord ++ tailWord_3021763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021763).length < 2 ^ (prefixWord ++ tailWord_3021763).sum := by decide
  have hdescent : baseEnd_3021763 < baseStart_3021763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021780 : List Nat := [2, 4, 1, 2, 1, 2, 10]
def baseStart_3021780 : Nat := 118140960795 + 3021780 * 2 ^ 59
def prefixEnd_3021780 : Nat := 4983230072969 + 3 ^ 40 * 3021780 * 2
def baseEnd_3021780 : Nat := 38311742522056605075385

theorem tailTrace_3021780 : CollatzResearch.WordTrace tailWord_3021780 prefixEnd_3021780 38311742522056605075385 := by
  unfold tailWord_3021780
  simp only [CollatzResearch.WordTrace]
  refine ⟨55106685496307306890983397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73475580661743075854644529 55106685496307306890983397)
  ·
    refine ⟨10332503530557620042059387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55106685496307306890983397 10332503530557620042059387)
    ·
      refine ⟨15498755295836430063089081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10332503530557620042059387 15498755295836430063089081)
      ·
        refine ⟨11624066471877322547316811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15498755295836430063089081 11624066471877322547316811)
        ·
          refine ⟨17436099707815983820975217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11624066471877322547316811 17436099707815983820975217)
          ·
            refine ⟨13077074780861987865731413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17436099707815983820975217 13077074780861987865731413)
            ·
              refine ⟨38311742522056605075385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13077074780861987865731413 38311742522056605075385)
              ·
                rfl

theorem cell22_3021780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 10].length) (baseStart_3021780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021780 prefixEnd_3021780 := by exact prefixLift 3021780
  have htrace : WordTrace (prefixWord ++ tailWord_3021780) baseStart_3021780 baseEnd_3021780 := by
    simpa [prefixWord, tailWord_3021780, baseEnd_3021780] using wordTrace_append hprefix tailTrace_3021780
  have hstable : (prefixWord ++ tailWord_3021780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021780).length < 2 ^ (prefixWord ++ tailWord_3021780).sum := by decide
  have hdescent : baseEnd_3021780 < baseStart_3021780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021829 : List Nat := [1, 3, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_3021829 : Nat := 118140960795 + 3021829 * 2 ^ 59
def prefixEnd_3021829 : Nat := 4983230072969 + 3 ^ 40 * 3021829 * 2
def baseEnd_3021829 : Nat := 1034433821796908542560245

theorem tailTrace_3021829 : CollatzResearch.WordTrace tailWord_3021829 prefixEnd_3021829 1034433821796908542560245 := by
  unfold tailWord_3021829
  simp only [CollatzResearch.WordTrace]
  refine ⟨110215158169437095150500541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73476772112958063433667027 110215158169437095150500541)
  ·
    refine ⟨41330684313538910681437703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110215158169437095150500541 41330684313538910681437703)
    ·
      refine ⟨61996026470308366022156555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41330684313538910681437703 61996026470308366022156555)
      ·
        refine ⟨92994039705462549033234833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61996026470308366022156555 92994039705462549033234833)
        ·
          refine ⟨69745529779096911774926125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92994039705462549033234833 69745529779096911774926125)
          ·
            refine ⟨26154573667161341915597297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69745529779096911774926125 26154573667161341915597297)
            ·
              refine ⟨19615930250371006436697973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26154573667161341915597297 19615930250371006436697973)
              ·
                refine ⟨1838993460972281853440435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19615930250371006436697973 1838993460972281853440435)
                ·
                  refine ⟨2758490191458422780160653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838993460972281853440435 2758490191458422780160653)
                  ·
                    refine ⟨1034433821796908542560245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2758490191458422780160653 1034433821796908542560245)
                    ·
                      rfl

theorem cell22_3021829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_3021829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021829 prefixEnd_3021829 := by exact prefixLift 3021829
  have htrace : WordTrace (prefixWord ++ tailWord_3021829) baseStart_3021829 baseEnd_3021829 := by
    simpa [prefixWord, tailWord_3021829, baseEnd_3021829] using wordTrace_append hprefix tailTrace_3021829
  have hstable : (prefixWord ++ tailWord_3021829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021829).length < 2 ^ (prefixWord ++ tailWord_3021829).sum := by decide
  have hdescent : baseEnd_3021829 < baseStart_3021829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021857 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3021857 : Nat := 118140960795 + 3021857 * 2 ^ 59
def prefixEnd_3021857 : Nat := 4983230072969 + 3 ^ 40 * 3021857 * 2
def baseEnd_3021857 : Nat := 1034443406769125802860159

theorem tailTrace_3021857 : CollatzResearch.WordTrace tailWord_3021857 prefixEnd_3021857 1034443406769125802860159 := by
  unfold tailWord_3021857
  simp only [CollatzResearch.WordTrace]
  refine ⟨110216179413335655932519825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73477452942223770621679883 110216179413335655932519825)
  ·
    refine ⟨82662134560001741949389869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110216179413335655932519825 82662134560001741949389869)
    ·
      refine ⟨30998300460000653231021201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82662134560001741949389869 30998300460000653231021201)
      ·
        refine ⟨23248725345000489923265901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30998300460000653231021201 23248725345000489923265901)
        ·
          refine ⟨8718272004375183721224713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23248725345000489923265901 8718272004375183721224713)
          ·
            refine ⟨6538704003281387790918535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8718272004375183721224713 6538704003281387790918535)
            ·
              refine ⟨9808056004922081686377803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538704003281387790918535 9808056004922081686377803)
              ·
                refine ⟨14712084007383122529566705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9808056004922081686377803 14712084007383122529566705)
                ·
                  refine ⟨11034063005537341897175029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14712084007383122529566705 11034063005537341897175029)
                  ·
                    refine ⟨1034443406769125802860159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11034063005537341897175029 1034443406769125802860159)
                    ·
                      rfl

theorem cell22_3021857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3021857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021857 prefixEnd_3021857 := by exact prefixLift 3021857
  have htrace : WordTrace (prefixWord ++ tailWord_3021857) baseStart_3021857 baseEnd_3021857 := by
    simpa [prefixWord, tailWord_3021857, baseEnd_3021857] using wordTrace_append hprefix tailTrace_3021857
  have hstable : (prefixWord ++ tailWord_3021857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021857).length < 2 ^ (prefixWord ++ tailWord_3021857).sum := by decide
  have hdescent : baseEnd_3021857 < baseStart_3021857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021872 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_3021872 : Nat := 118140960795 + 3021872 * 2 ^ 59
def prefixEnd_3021872 : Nat := 4983230072969 + 3 ^ 40 * 3021872 * 2
def baseEnd_3021872 : Nat := 1034448541575670763735113

theorem tailTrace_3021872 : CollatzResearch.WordTrace tailWord_3021872 prefixEnd_3021872 1034448541575670763735113 := by
  unfold tailWord_3021872
  simp only [CollatzResearch.WordTrace]
  refine ⟨55108363254140656747157935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73477817672187542329543913 55108363254140656747157935)
  ·
    refine ⟨82662544881210985120736903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55108363254140656747157935 82662544881210985120736903)
    ·
      refine ⟨123993817321816477681105355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82662544881210985120736903 123993817321816477681105355)
      ·
        refine ⟨185990725982724716521658033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123993817321816477681105355 185990725982724716521658033)
        ·
          refine ⟨139493044487043537391243525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185990725982724716521658033 139493044487043537391243525)
          ·
            refine ⟨26154945841320663260858161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139493044487043537391243525 26154945841320663260858161)
            ·
              refine ⟨19616209380990497445643621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26154945841320663260858161 19616209380990497445643621)
              ·
                refine ⟨3678039258935718271058179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19616209380990497445643621 3678039258935718271058179)
                ·
                  refine ⟨5517058888403577406587269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678039258935718271058179 5517058888403577406587269)
                  ·
                    refine ⟨1034448541575670763735113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5517058888403577406587269 1034448541575670763735113)
                    ·
                      rfl

theorem cell22_3021872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_3021872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021872 prefixEnd_3021872 := by exact prefixLift 3021872
  have htrace : WordTrace (prefixWord ++ tailWord_3021872) baseStart_3021872 baseEnd_3021872 := by
    simpa [prefixWord, tailWord_3021872, baseEnd_3021872] using wordTrace_append hprefix tailTrace_3021872
  have hstable : (prefixWord ++ tailWord_3021872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021872).length < 2 ^ (prefixWord ++ tailWord_3021872).sum := by decide
  have hdescent : baseEnd_3021872 < baseStart_3021872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021947 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 5, 3]
def baseStart_3021947 : Nat := 118140960795 + 3021947 * 2 ^ 59
def prefixEnd_3021947 : Nat := 4983230072969 + 3 ^ 40 * 3021947 * 2
def baseEnd_3021947 : Nat := 1034474215608395568109883

theorem tailTrace_3021947 : CollatzResearch.WordTrace tailWord_3021947 prefixEnd_3021947 1034474215608395568109883 := by
  unfold tailWord_3021947
  simp only [CollatzResearch.WordTrace]
  refine ⟨110219461983009601303296095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73479641322006400868864063 110219461983009601303296095)
  ·
    refine ⟨165329192974514401954944143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110219461983009601303296095 165329192974514401954944143)
    ·
      refine ⟨247993789461771602932416215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165329192974514401954944143 247993789461771602932416215)
      ·
        refine ⟨371990684192657404398624323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247993789461771602932416215 371990684192657404398624323)
        ·
          refine ⟨557986026288986106597936485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371990684192657404398624323 557986026288986106597936485)
          ·
            refine ⟨104622379929184894987113091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 557986026288986106597936485 104622379929184894987113091)
            ·
              refine ⟨156933569893777342480669637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104622379929184894987113091 156933569893777342480669637)
              ·
                refine ⟨29425044355083251715125557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156933569893777342480669637 29425044355083251715125557)
                ·
                  refine ⟨2758597908289054848293021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29425044355083251715125557 2758597908289054848293021)
                  ·
                    refine ⟨1034474215608395568109883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2758597908289054848293021 1034474215608395568109883)
                    ·
                      rfl

theorem cell22_3021947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 3].length) (baseStart_3021947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021947 prefixEnd_3021947 := by exact prefixLift 3021947
  have htrace : WordTrace (prefixWord ++ tailWord_3021947) baseStart_3021947 baseEnd_3021947 := by
    simpa [prefixWord, tailWord_3021947, baseEnd_3021947] using wordTrace_append hprefix tailTrace_3021947
  have hstable : (prefixWord ++ tailWord_3021947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021947).length < 2 ^ (prefixWord ++ tailWord_3021947).sum := by decide
  have hdescent : baseEnd_3021947 < baseStart_3021947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021962 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3021962 : Nat := 118140960795 + 3021962 * 2 ^ 59
def prefixEnd_3021962 : Nat := 4983230072969 + 3 ^ 40 * 3021962 * 2
def baseEnd_3021962 : Nat := 1034479350414940528984837

theorem tailTrace_3021962 : CollatzResearch.WordTrace tailWord_3021962 prefixEnd_3021962 1034479350414940528984837 := by
  unfold tailWord_3021962
  simp only [CollatzResearch.WordTrace]
  refine ⟨27555002269488814716273035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73480006051970172576728093 27555002269488814716273035)
  ·
    refine ⟨41332503404233222074409553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27555002269488814716273035 41332503404233222074409553)
    ·
      refine ⟨30999377553174916555807165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41332503404233222074409553 30999377553174916555807165)
      ·
        refine ⟨11624766582440593708427687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30999377553174916555807165 11624766582440593708427687)
        ·
          refine ⟨17437149873660890562641531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11624766582440593708427687 17437149873660890562641531)
          ·
            refine ⟨26155724810491335843962297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17437149873660890562641531 26155724810491335843962297)
            ·
              refine ⟨19616793607868501882971723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26155724810491335843962297 19616793607868501882971723)
              ·
                refine ⟨29425190411802752824457585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19616793607868501882971723 29425190411802752824457585)
                ·
                  refine ⟨22068892808852064618343189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29425190411802752824457585 22068892808852064618343189)
                  ·
                    refine ⟨1034479350414940528984837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22068892808852064618343189 1034479350414940528984837)
                    ·
                      rfl

theorem cell22_3021962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3021962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3021962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3021962 prefixEnd_3021962 := by exact prefixLift 3021962
  have htrace : WordTrace (prefixWord ++ tailWord_3021962) baseStart_3021962 baseEnd_3021962 := by
    simpa [prefixWord, tailWord_3021962, baseEnd_3021962] using wordTrace_append hprefix tailTrace_3021962
  have hstable : (prefixWord ++ tailWord_3021962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021962).length < 2 ^ (prefixWord ++ tailWord_3021962).sum := by decide
  have hdescent : baseEnd_3021962 < baseStart_3021962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022056 : List Nat := [2, 1, 4, 1, 2, 1, 4, 3, 4]
def baseStart_3022056 : Nat := 118140960795 + 3022056 * 2 ^ 59
def prefixEnd_3022056 : Nat := 4983230072969 + 3 ^ 40 * 3022056 * 2
def baseEnd_3022056 : Nat := 344837176178651872378183

theorem tailTrace_3022056 : CollatzResearch.WordTrace tailWord_3022056 prefixEnd_3022056 344837176178651872378183 := by
  unfold tailWord_3022056
  simp only [CollatzResearch.WordTrace]
  refine ⟨55111718769807356459507011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73482291693076475279342681 55111718769807356459507011)
  ·
    refine ⟨82667578154711034689260517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55111718769807356459507011 82667578154711034689260517)
    ·
      refine ⟨15500170904008319004236347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82667578154711034689260517 15500170904008319004236347)
      ·
        refine ⟨23250256356012478506354521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15500170904008319004236347 23250256356012478506354521)
        ·
          refine ⟨17437692267009358879765891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23250256356012478506354521 17437692267009358879765891)
          ·
            refine ⟨26156538400514038319648837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17437692267009358879765891 26156538400514038319648837)
            ·
              refine ⟨4904350950096382184934157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26156538400514038319648837 4904350950096382184934157)
              ·
                refine ⟨1839131606286143319350309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4904350950096382184934157 1839131606286143319350309)
                ·
                  refine ⟨344837176178651872378183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1839131606286143319350309 344837176178651872378183)
                  ·
                    rfl

theorem cell22_3022056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 4].length) (baseStart_3022056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022056 prefixEnd_3022056 := by exact prefixLift 3022056
  have htrace : WordTrace (prefixWord ++ tailWord_3022056) baseStart_3022056 baseEnd_3022056 := by
    simpa [prefixWord, tailWord_3022056, baseEnd_3022056] using wordTrace_append hprefix tailTrace_3022056
  have hstable : (prefixWord ++ tailWord_3022056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022056).length < 2 ^ (prefixWord ++ tailWord_3022056).sum := by decide
  have hdescent : baseEnd_3022056 < baseStart_3022056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022058 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_3022058 : Nat := 118140960795 + 3022058 * 2 ^ 59
def prefixEnd_3022058 : Nat := 4983230072969 + 3 ^ 40 * 3022058 * 2
def baseEnd_3022058 : Nat := 1034512213176828278584543

theorem tailTrace_3022058 : CollatzResearch.WordTrace tailWord_3022058 prefixEnd_3022058 1034512213176828278584543 := by
  unfold tailWord_3022058
  simp only [CollatzResearch.WordTrace]
  refine ⟨27555877621401866815146707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73482340323738311507057885 27555877621401866815146707)
  ·
    refine ⟨41333816432102800222720061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27555877621401866815146707 41333816432102800222720061)
    ·
      refine ⟨15500181162038550083520023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41333816432102800222720061 15500181162038550083520023)
      ·
        refine ⟨23250271743057825125280035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15500181162038550083520023 23250271743057825125280035)
        ·
          refine ⟨34875407614586737687920053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23250271743057825125280035 34875407614586737687920053)
          ·
            refine ⟨3269569463867506658242505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34875407614586737687920053 3269569463867506658242505)
            ·
              refine ⟨2452177097900629993681879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3269569463867506658242505 2452177097900629993681879)
              ·
                refine ⟨3678265646850944990522819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452177097900629993681879 3678265646850944990522819)
                ·
                  refine ⟨5517398470276417485784229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678265646850944990522819 5517398470276417485784229)
                  ·
                    refine ⟨1034512213176828278584543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5517398470276417485784229 1034512213176828278584543)
                    ·
                      rfl

theorem cell22_3022058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_3022058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022058 prefixEnd_3022058 := by exact prefixLift 3022058
  have htrace : WordTrace (prefixWord ++ tailWord_3022058) baseStart_3022058 baseEnd_3022058 := by
    simpa [prefixWord, tailWord_3022058, baseEnd_3022058] using wordTrace_append hprefix tailTrace_3022058
  have hstable : (prefixWord ++ tailWord_3022058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022058).length < 2 ^ (prefixWord ++ tailWord_3022058).sum := by decide
  have hdescent : baseEnd_3022058 < baseStart_3022058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022067 : List Nat := [1, 1, 1, 2, 2, 6, 9]
def baseStart_3022067 : Nat := 118140960795 + 3022067 * 2 ^ 59
def prefixEnd_3022067 : Nat := 4983230072969 + 3 ^ 40 * 3022067 * 2
def baseEnd_3022067 : Nat := 38315381261509453892945

theorem tailTrace_3022067 : CollatzResearch.WordTrace tailWord_3022067 prefixEnd_3022067 38315381261509453892945 := by
  unfold tailWord_3022067
  simp only [CollatzResearch.WordTrace]
  refine ⟨110223838742574861797664455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73482559161716574531776303 110223838742574861797664455)
  ·
    refine ⟨165335758113862292696496683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110223838742574861797664455 165335758113862292696496683)
    ·
      refine ⟨248003637170793439044745025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165335758113862292696496683 248003637170793439044745025)
      ·
        refine ⟨186002727878095079283558769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248003637170793439044745025 186002727878095079283558769)
        ·
          refine ⟨139502045908571309462669077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186002727878095079283558769 139502045908571309462669077)
          ·
            refine ⟨6539158401964280131062613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139502045908571309462669077 6539158401964280131062613)
            ·
              refine ⟨38315381261509453892945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6539158401964280131062613 38315381261509453892945)
              ·
                rfl

theorem cell22_3022067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 9].length) (baseStart_3022067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022067 prefixEnd_3022067 := by exact prefixLift 3022067
  have htrace : WordTrace (prefixWord ++ tailWord_3022067) baseStart_3022067 baseEnd_3022067 := by
    simpa [prefixWord, tailWord_3022067, baseEnd_3022067] using wordTrace_append hprefix tailTrace_3022067
  have hstable : (prefixWord ++ tailWord_3022067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022067).length < 2 ^ (prefixWord ++ tailWord_3022067).sum := by decide
  have hdescent : baseEnd_3022067 < baseStart_3022067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022088 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 1, 5]
def baseStart_3022088 : Nat := 118140960795 + 3022088 * 2 ^ 59
def prefixEnd_3022088 : Nat := 4983230072969 + 3 ^ 40 * 3022088 * 2
def baseEnd_3022088 : Nat := 1034522482789918200334451

theorem tailTrace_3022088 : CollatzResearch.WordTrace tailWord_3022088 prefixEnd_3022088 1034522482789918200334451 := by
  unfold tailWord_3022088
  simp only [CollatzResearch.WordTrace]
  refine ⟨55112302337749391192089459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73483069783665854922785945 55112302337749391192089459)
  ·
    refine ⟨82668453506624086788134189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55112302337749391192089459 82668453506624086788134189)
    ·
      refine ⟨31000670064984032545550321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82668453506624086788134189 31000670064984032545550321)
      ·
        refine ⟨23250502548738024409162741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31000670064984032545550321 23250502548738024409162741)
        ·
          refine ⟨2179734613944189788359007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23250502548738024409162741 2179734613944189788359007)
          ·
            refine ⟨3269601920916284682538511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179734613944189788359007 3269601920916284682538511)
            ·
              refine ⟨4904402881374427023807767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269601920916284682538511 4904402881374427023807767)
              ·
                refine ⟨7356604322061640535711651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4904402881374427023807767 7356604322061640535711651)
                ·
                  refine ⟨11034906483092460803567477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7356604322061640535711651 11034906483092460803567477)
                  ·
                    refine ⟨1034522482789918200334451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11034906483092460803567477 1034522482789918200334451)
                    ·
                      rfl

theorem cell22_3022088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_3022088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022088 prefixEnd_3022088 := by exact prefixLift 3022088
  have htrace : WordTrace (prefixWord ++ tailWord_3022088) baseStart_3022088 baseEnd_3022088 := by
    simpa [prefixWord, tailWord_3022088, baseEnd_3022088] using wordTrace_append hprefix tailTrace_3022088
  have hstable : (prefixWord ++ tailWord_3022088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022088).length < 2 ^ (prefixWord ++ tailWord_3022088).sum := by decide
  have hdescent : baseEnd_3022088 < baseStart_3022088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022129 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 7]
def baseStart_3022129 : Nat := 118140960795 + 3022129 * 2 ^ 59
def prefixEnd_3022129 : Nat := 4983230072969 + 3 ^ 40 * 3022129 * 2
def baseEnd_3022129 : Nat := 344845505975935920019775

theorem tailTrace_3022129 : CollatzResearch.WordTrace tailWord_3022129 prefixEnd_3022129 344845505975935920019775 := by
  unfold tailWord_3022129
  simp only [CollatzResearch.WordTrace]
  refine ⟨110226100068350246386421441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73484066712233497590947627 110226100068350246386421441)
  ·
    refine ⟨82669575051262684789816081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110226100068350246386421441 82669575051262684789816081)
    ·
      refine ⟨62002181288447013592362061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82669575051262684789816081 62002181288447013592362061)
      ·
        refine ⟨23250817983167630097135773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62002181288447013592362061 23250817983167630097135773)
        ·
          refine ⟨8719056743687861286425915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23250817983167630097135773 8719056743687861286425915)
          ·
            refine ⟨13078585115531791929638873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8719056743687861286425915 13078585115531791929638873)
            ·
              refine ⟨9808938836648843947229155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13078585115531791929638873 9808938836648843947229155)
              ·
                refine ⟨14713408254973265920843733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9808938836648843947229155 14713408254973265920843733)
                ·
                  refine ⟨344845505975935920019775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14713408254973265920843733 344845505975935920019775)
                  ·
                    rfl

theorem cell22_3022129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_3022129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022129 prefixEnd_3022129 := by exact prefixLift 3022129
  have htrace : WordTrace (prefixWord ++ tailWord_3022129) baseStart_3022129 baseEnd_3022129 := by
    simpa [prefixWord, tailWord_3022129, baseEnd_3022129] using wordTrace_append hprefix tailTrace_3022129
  have hstable : (prefixWord ++ tailWord_3022129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022129).length < 2 ^ (prefixWord ++ tailWord_3022129).sum := by decide
  have hdescent : baseEnd_3022129 < baseStart_3022129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022133 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_3022133 : Nat := 118140960795 + 3022133 * 2 ^ 59
def prefixEnd_3022133 : Nat := 4983230072969 + 3 ^ 40 * 3022133 * 2
def baseEnd_3022133 : Nat := 1034537887209553082959313

theorem tailTrace_3022133 : CollatzResearch.WordTrace tailWord_3022133 prefixEnd_3022133 1034537887209553082959313 := by
  unfold tailWord_3022133
  simp only [CollatzResearch.WordTrace]
  refine ⟨110226245960335755069567053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73484163973557170046378035 110226245960335755069567053)
  ·
    refine ⟨41334842235125908151087645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110226245960335755069567053 41334842235125908151087645)
    ·
      refine ⟨15500565838172215556657867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41334842235125908151087645 15500565838172215556657867)
      ·
        refine ⟨23250848757258323334986801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15500565838172215556657867 23250848757258323334986801)
        ·
          refine ⟨17438136567943742501240101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23250848757258323334986801 17438136567943742501240101)
          ·
            refine ⟨3269650606489451718982519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17438136567943742501240101 3269650606489451718982519)
            ·
              refine ⟨4904475909734177578473779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269650606489451718982519 4904475909734177578473779)
              ·
                refine ⟨7356713864601266367710669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4904475909734177578473779 7356713864601266367710669)
                ·
                  refine ⟨2758767699225474887891501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7356713864601266367710669 2758767699225474887891501)
                  ·
                    refine ⟨1034537887209553082959313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2758767699225474887891501 1034537887209553082959313)
                    ·
                      rfl

theorem cell22_3022133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_3022133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022133 prefixEnd_3022133 := by exact prefixLift 3022133
  have htrace : WordTrace (prefixWord ++ tailWord_3022133) baseStart_3022133 baseEnd_3022133 := by
    simpa [prefixWord, tailWord_3022133, baseEnd_3022133] using wordTrace_append hprefix tailTrace_3022133
  have hstable : (prefixWord ++ tailWord_3022133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022133).length < 2 ^ (prefixWord ++ tailWord_3022133).sum := by decide
  have hdescent : baseEnd_3022133 < baseStart_3022133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022184 : List Nat := [2, 1, 4, 2, 4, 1, 2, 2, 1, 3]
def baseStart_3022184 : Nat := 118140960795 + 3022184 * 2 ^ 59
def prefixEnd_3022184 : Nat := 4983230072969 + 3 ^ 40 * 3022184 * 2
def baseEnd_3022184 : Nat := 1034555345551805949934157

theorem tailTrace_3022184 : CollatzResearch.WordTrace tailWord_3022184 prefixEnd_3022184 1034555345551805949934157 := by
  unfold tailWord_3022184
  simp only [CollatzResearch.WordTrace]
  refine ⟨55114053041575495389836803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73485404055433993853115737 55114053041575495389836803)
  ·
    refine ⟨82671079562363243084755205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55114053041575495389836803 82671079562363243084755205)
    ·
      refine ⟨15500827417943108078391601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82671079562363243084755205 15500827417943108078391601)
      ·
        refine ⟨11625620563457331058793701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15500827417943108078391601 11625620563457331058793701)
        ·
          refine ⟨2179803855648249573523819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11625620563457331058793701 2179803855648249573523819)
          ·
            refine ⟨3269705783472374360285729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179803855648249573523819 3269705783472374360285729)
            ·
              refine ⟨2452279337604280770214297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3269705783472374360285729 2452279337604280770214297)
              ·
                refine ⟨1839209503203210577660723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452279337604280770214297 1839209503203210577660723)
                ·
                  refine ⟨2758814254804815866491085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839209503203210577660723 2758814254804815866491085)
                  ·
                    refine ⟨1034555345551805949934157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2758814254804815866491085 1034555345551805949934157)
                    ·
                      rfl

theorem cell22_3022184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_3022184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022184 prefixEnd_3022184 := by exact prefixLift 3022184
  have htrace : WordTrace (prefixWord ++ tailWord_3022184) baseStart_3022184 baseEnd_3022184 := by
    simpa [prefixWord, tailWord_3022184, baseEnd_3022184] using wordTrace_append hprefix tailTrace_3022184
  have hstable : (prefixWord ++ tailWord_3022184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022184).length < 2 ^ (prefixWord ++ tailWord_3022184).sum := by decide
  have hdescent : baseEnd_3022184 < baseStart_3022184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022191 : List Nat := [1, 1, 2, 1, 3, 1, 5, 4, 4]
def baseStart_3022191 : Nat := 118140960795 + 3022191 * 2 ^ 59
def prefixEnd_3022191 : Nat := 4983230072969 + 3 ^ 40 * 3022191 * 2
def baseEnd_3022191 : Nat := 344852580598286755003045

theorem tailTrace_3022191 : CollatzResearch.WordTrace tailWord_3022191 prefixEnd_3022191 344852580598286755003045 := by
  unfold tailWord_3022191
  simp only [CollatzResearch.WordTrace]
  refine ⟨110228361394125630975178427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73485574262750420650118951 110228361394125630975178427)
  ·
    refine ⟨165342542091188446462767641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110228361394125630975178427 165342542091188446462767641)
    ·
      refine ⟨124006906568391334847075731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165342542091188446462767641 124006906568391334847075731)
      ·
        refine ⟨186010359852587002270613597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124006906568391334847075731 186010359852587002270613597)
        ·
          refine ⟨69753884944720125851480099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186010359852587002270613597 69753884944720125851480099)
          ·
            refine ⟨104630827417080188777220149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69753884944720125851480099 104630827417080188777220149)
            ·
              refine ⟨9809140070351267697864389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104630827417080188777220149 9809140070351267697864389)
              ·
                refine ⟨1839213763190862693349573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9809140070351267697864389 1839213763190862693349573)
                ·
                  refine ⟨344852580598286755003045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1839213763190862693349573 344852580598286755003045)
                  ·
                    rfl

theorem cell22_3022191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 4].length) (baseStart_3022191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022191 prefixEnd_3022191 := by exact prefixLift 3022191
  have htrace : WordTrace (prefixWord ++ tailWord_3022191) baseStart_3022191 baseEnd_3022191 := by
    simpa [prefixWord, tailWord_3022191, baseEnd_3022191] using wordTrace_append hprefix tailTrace_3022191
  have hstable : (prefixWord ++ tailWord_3022191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022191).length < 2 ^ (prefixWord ++ tailWord_3022191).sum := by decide
  have hdescent : baseEnd_3022191 < baseStart_3022191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022204 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_3022204 : Nat := 118140960795 + 3022204 * 2 ^ 59
def prefixEnd_3022204 : Nat := 4983230072969 + 3 ^ 40 * 3022204 * 2
def baseEnd_3022204 : Nat := 1034562191960532564434095

theorem tailTrace_3022204 : CollatzResearch.WordTrace tailWord_3022204 prefixEnd_3022204 1034562191960532564434095 := by
  unfold tailWord_3022204
  simp only [CollatzResearch.WordTrace]
  refine ⟨55114417771539267097700833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73485890362052356130267777 55114417771539267097700833)
  ·
    refine ⟨41335813328654450323275625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55114417771539267097700833 41335813328654450323275625)
    ·
      refine ⟨31001859996490837742456719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41335813328654450323275625 31001859996490837742456719)
      ·
        refine ⟨46502789994736256613685079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31001859996490837742456719 46502789994736256613685079)
        ·
          refine ⟨69754184992104384920527619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46502789994736256613685079 69754184992104384920527619)
          ·
            refine ⟨104631277488156577380791429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69754184992104384920527619 104631277488156577380791429)
            ·
              refine ⟨19618364529029358258898393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104631277488156577380791429 19618364529029358258898393)
              ·
                refine ⟨14713773396772018694173795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19618364529029358258898393 14713773396772018694173795)
                ·
                  refine ⟨22070660095158028041260693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14713773396772018694173795 22070660095158028041260693)
                  ·
                    refine ⟨1034562191960532564434095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22070660095158028041260693 1034562191960532564434095)
                    ·
                      rfl

theorem cell22_3022204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_3022204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022204 prefixEnd_3022204 := by exact prefixLift 3022204
  have htrace : WordTrace (prefixWord ++ tailWord_3022204) baseStart_3022204 baseEnd_3022204 := by
    simpa [prefixWord, tailWord_3022204, baseEnd_3022204] using wordTrace_append hprefix tailTrace_3022204
  have hstable : (prefixWord ++ tailWord_3022204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022204).length < 2 ^ (prefixWord ++ tailWord_3022204).sum := by decide
  have hdescent : baseEnd_3022204 < baseStart_3022204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022328 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_3022328 : Nat := 118140960795 + 3022328 * 2 ^ 59
def prefixEnd_3022328 : Nat := 4983230072969 + 3 ^ 40 * 3022328 * 2
def baseEnd_3022328 : Nat := 1034604639694637574333715

theorem tailTrace_3022328 : CollatzResearch.WordTrace tailWord_3022328 prefixEnd_3022328 1034604639694637574333715 := by
  unfold tailWord_3022328
  simp only [CollatzResearch.WordTrace]
  refine ⟨55116679097314651686457819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73488905463086202248610425 55116679097314651686457819)
  ·
    refine ⟨82675018645971977529686729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55116679097314651686457819 82675018645971977529686729)
    ·
      refine ⟨62006263984478983147265047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82675018645971977529686729 62006263984478983147265047)
      ·
        refine ⟨93009395976718474720897571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62006263984478983147265047 93009395976718474720897571)
        ·
          refine ⟨139514093965077712081346357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93009395976718474720897571 139514093965077712081346357)
          ·
            refine ⟨13079446309226035507626221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139514093965077712081346357 13079446309226035507626221)
            ·
              refine ⟨4904792365959763315359833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13079446309226035507626221 4904792365959763315359833)
              ·
                refine ⟨3678594274469822486519875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4904792365959763315359833 3678594274469822486519875)
                ·
                  refine ⟨5517891411704733729779813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678594274469822486519875 5517891411704733729779813)
                  ·
                    refine ⟨1034604639694637574333715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5517891411704733729779813 1034604639694637574333715)
                    ·
                      rfl

theorem cell22_3022328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_3022328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022328 prefixEnd_3022328 := by exact prefixLift 3022328
  have htrace : WordTrace (prefixWord ++ tailWord_3022328) baseStart_3022328 baseEnd_3022328 := by
    simpa [prefixWord, tailWord_3022328, baseEnd_3022328] using wordTrace_append hprefix tailTrace_3022328
  have hstable : (prefixWord ++ tailWord_3022328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022328).length < 2 ^ (prefixWord ++ tailWord_3022328).sum := by decide
  have hdescent : baseEnd_3022328 < baseStart_3022328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022360 : List Nat := [2, 1, 2, 3, 4, 1, 1, 4, 4]
def baseStart_3022360 : Nat := 118140960795 + 3022360 * 2 ^ 59
def prefixEnd_3022360 : Nat := 4983230072969 + 3 ^ 40 * 3022360 * 2
def baseEnd_3022360 : Nat := 344871864649533385844539

theorem tailTrace_3022360 : CollatzResearch.WordTrace tailWord_3022360 prefixEnd_3022360 344871864649533385844539 := by
  unfold tailWord_3022360
  simp only [CollatzResearch.WordTrace]
  refine ⟨55117262665256686419040267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73489683553675581892053689 55117262665256686419040267)
  ·
    refine ⟨82675893997885029628560401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55117262665256686419040267 82675893997885029628560401)
    ·
      refine ⟨62006920498413772221420301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82675893997885029628560401 62006920498413772221420301)
      ·
        refine ⟨23252595186905164583032613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62006920498413772221420301 23252595186905164583032613)
        ·
          refine ⟨4359861597544718359318615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23252595186905164583032613 4359861597544718359318615)
          ·
            refine ⟨6539792396317077538977923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4359861597544718359318615 6539792396317077538977923)
            ·
              refine ⟨9809688594475616308466885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539792396317077538977923 9809688594475616308466885)
              ·
                refine ⟨1839316611464178057837541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9809688594475616308466885 1839316611464178057837541)
                ·
                  refine ⟨344871864649533385844539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1839316611464178057837541 344871864649533385844539)
                  ·
                    rfl

theorem cell22_3022360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 4].length) (baseStart_3022360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022360 prefixEnd_3022360 := by exact prefixLift 3022360
  have htrace : WordTrace (prefixWord ++ tailWord_3022360) baseStart_3022360 baseEnd_3022360 := by
    simpa [prefixWord, tailWord_3022360, baseEnd_3022360] using wordTrace_append hprefix tailTrace_3022360
  have hstable : (prefixWord ++ tailWord_3022360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022360).length < 2 ^ (prefixWord ++ tailWord_3022360).sum := by decide
  have hdescent : baseEnd_3022360 < baseStart_3022360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022390 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3022390 : Nat := 118140960795 + 3022390 * 2 ^ 59
def prefixEnd_3022390 : Nat := 4983230072969 + 3 ^ 40 * 3022390 * 2
def baseEnd_3022390 : Nat := 1034625863561690079283525

theorem tailTrace_3022390 : CollatzResearch.WordTrace tailWord_3022390 prefixEnd_3022390 1034625863561690079283525 := by
  unfold tailWord_3022390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6889726220025292997604539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73490413013603125307781749 6889726220025292997604539)
  ·
    refine ⟨10334589330037939496406809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6889726220025292997604539 10334589330037939496406809)
    ·
      refine ⟨7750941997528454622305107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10334589330037939496406809 7750941997528454622305107)
      ·
        refine ⟨11626412996292681933457661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7750941997528454622305107 11626412996292681933457661)
        ·
          refine ⟨4359904873609755725046623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11626412996292681933457661 4359904873609755725046623)
          ·
            refine ⟨6539857310414633587569935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4359904873609755725046623 6539857310414633587569935)
            ·
              refine ⟨9809785965621950381354903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539857310414633587569935 9809785965621950381354903)
              ·
                refine ⟨14714678948432925572032355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809785965621950381354903 14714678948432925572032355)
                ·
                  refine ⟨22072018422649388358048533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14714678948432925572032355 22072018422649388358048533)
                  ·
                    refine ⟨1034625863561690079283525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22072018422649388358048533 1034625863561690079283525)
                    ·
                      rfl

theorem cell22_3022390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3022390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022390 prefixEnd_3022390 := by exact prefixLift 3022390
  have htrace : WordTrace (prefixWord ++ tailWord_3022390) baseStart_3022390 baseEnd_3022390 := by
    simpa [prefixWord, tailWord_3022390, baseEnd_3022390] using wordTrace_append hprefix tailTrace_3022390
  have hstable : (prefixWord ++ tailWord_3022390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022390).length < 2 ^ (prefixWord ++ tailWord_3022390).sum := by decide
  have hdescent : baseEnd_3022390 < baseStart_3022390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022416 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 7]
def baseStart_3022416 : Nat := 118140960795 + 3022416 * 2 ^ 59
def prefixEnd_3022416 : Nat := 4983230072969 + 3 ^ 40 * 3022416 * 2
def baseEnd_3022416 : Nat := 344878254631011559377815

theorem tailTrace_3022416 : CollatzResearch.WordTrace tailWord_3022416 prefixEnd_3022416 344878254631011559377815 := by
  unfold tailWord_3022416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55118283909155247201059551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73491045212206996268079401 55118283909155247201059551)
  ·
    refine ⟨82677425863732870801589327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55118283909155247201059551 82677425863732870801589327)
    ·
      refine ⟨124016138795599306202383991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82677425863732870801589327 124016138795599306202383991)
      ·
        refine ⟨186024208193398959303575987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124016138795599306202383991 186024208193398959303575987)
        ·
          refine ⟨279036312290098438955363981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186024208193398959303575987 279036312290098438955363981)
          ·
            refine ⟨104638617108786914608261493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279036312290098438955363981 104638617108786914608261493)
            ·
              refine ⟨9809870353948773244524515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104638617108786914608261493 9809870353948773244524515)
              ·
                refine ⟨14714805530923159866786773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809870353948773244524515 14714805530923159866786773)
                ·
                  refine ⟨344878254631011559377815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14714805530923159866786773 344878254631011559377815)
                  ·
                    rfl

theorem cell22_3022416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_3022416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022416 prefixEnd_3022416 := by exact prefixLift 3022416
  have htrace : WordTrace (prefixWord ++ tailWord_3022416) baseStart_3022416 baseEnd_3022416 := by
    simpa [prefixWord, tailWord_3022416, baseEnd_3022416] using wordTrace_append hprefix tailTrace_3022416
  have hstable : (prefixWord ++ tailWord_3022416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022416).length < 2 ^ (prefixWord ++ tailWord_3022416).sum := by decide
  have hdescent : baseEnd_3022416 < baseStart_3022416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022420 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3022420 : Nat := 118140960795 + 3022420 * 2 ^ 59
def prefixEnd_3022420 : Nat := 4983230072969 + 3 ^ 40 * 3022420 * 2
def baseEnd_3022420 : Nat := 1034636133174780001033433

theorem tailTrace_3022420 : CollatzResearch.WordTrace tailWord_3022420 prefixEnd_3022420 1034636133174780001033433 := by
  unfold tailWord_3022420
  simp only [CollatzResearch.WordTrace]
  refine ⟨55118356855148001542632357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73491142473530668723509809 55118356855148001542632357)
  ·
    refine ⟨10334691910340250289243567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55118356855148001542632357 10334691910340250289243567)
    ·
      refine ⟨15502037865510375433865351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10334691910340250289243567 15502037865510375433865351)
      ·
        refine ⟨23253056798265563150798027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15502037865510375433865351 23253056798265563150798027)
        ·
          refine ⟨34879585197398344726197041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23253056798265563150798027 34879585197398344726197041)
          ·
            refine ⟨26159688898048758544647781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34879585197398344726197041 26159688898048758544647781)
            ·
              refine ⟨4904941668384142227121459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26159688898048758544647781 4904941668384142227121459)
              ·
                refine ⟨7357412502576213340682189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4904941668384142227121459 7357412502576213340682189)
                ·
                  refine ⟨2759029688466080002755821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7357412502576213340682189 2759029688466080002755821)
                  ·
                    refine ⟨1034636133174780001033433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2759029688466080002755821 1034636133174780001033433)
                    ·
                      rfl

theorem cell22_3022420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3022420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022420 prefixEnd_3022420 := by exact prefixLift 3022420
  have htrace : WordTrace (prefixWord ++ tailWord_3022420) baseStart_3022420 baseEnd_3022420 := by
    simpa [prefixWord, tailWord_3022420, baseEnd_3022420] using wordTrace_append hprefix tailTrace_3022420
  have hstable : (prefixWord ++ tailWord_3022420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022420).length < 2 ^ (prefixWord ++ tailWord_3022420).sum := by decide
  have hdescent : baseEnd_3022420 < baseStart_3022420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022454 : List Nat := [5, 1, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_3022454 : Nat := 118140960795 + 3022454 * 2 ^ 59
def prefixEnd_3022454 : Nat := 4983230072969 + 3 ^ 40 * 3022454 * 2
def baseEnd_3022454 : Nat := 1034647772069615245683329

theorem tailTrace_3022454 : CollatzResearch.WordTrace tailWord_3022454 prefixEnd_3022454 1034647772069615245683329 := by
  unfold tailWord_3022454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6889872112010801680750151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73491969194781884594668277 6889872112010801680750151)
  ·
    refine ⟨10334808168016202521125227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6889872112010801680750151 10334808168016202521125227)
    ·
      refine ⟨15502212252024303781687841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10334808168016202521125227 15502212252024303781687841)
      ·
        refine ⟨11626659189018227836265881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15502212252024303781687841 11626659189018227836265881)
        ·
          refine ⟨8719994391763670877199411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11626659189018227836265881 8719994391763670877199411)
          ·
            refine ⟨13079991587645506315799117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8719994391763670877199411 13079991587645506315799117)
            ·
              refine ⟨4904996845367064868424669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13079991587645506315799117 4904996845367064868424669)
              ·
                refine ⟨1839373817012649325659251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4904996845367064868424669 1839373817012649325659251)
                ·
                  refine ⟨2759060725518973988488877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839373817012649325659251 2759060725518973988488877)
                  ·
                    refine ⟨1034647772069615245683329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2759060725518973988488877 1034647772069615245683329)
                    ·
                      rfl

theorem cell22_3022454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_3022454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022454 prefixEnd_3022454 := by exact prefixLift 3022454
  have htrace : WordTrace (prefixWord ++ tailWord_3022454) baseStart_3022454 baseEnd_3022454 := by
    simpa [prefixWord, tailWord_3022454, baseEnd_3022454] using wordTrace_append hprefix tailTrace_3022454
  have hstable : (prefixWord ++ tailWord_3022454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022454).length < 2 ^ (prefixWord ++ tailWord_3022454).sum := by decide
  have hdescent : baseEnd_3022454 < baseStart_3022454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022484 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 5]
def baseStart_3022484 : Nat := 118140960795 + 3022484 * 2 ^ 59
def prefixEnd_3022484 : Nat := 4983230072969 + 3 ^ 40 * 3022484 * 2
def baseEnd_3022484 : Nat := 344886013894235055811079

theorem tailTrace_3022484 : CollatzResearch.WordTrace tailWord_3022484 prefixEnd_3022484 344886013894235055811079 := by
  unfold tailWord_3022484
  simp only [CollatzResearch.WordTrace]
  refine ⟨55119523991032071007797253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73492698654709428010396337 55119523991032071007797253)
  ·
    refine ⟨10334910748318513313961985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55119523991032071007797253 10334910748318513313961985)
    ·
      refine ⟨7751183061238884985471489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10334910748318513313961985 7751183061238884985471489)
      ·
        refine ⟨5813387295929163739103617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7751183061238884985471489 5813387295929163739103617)
        ·
          refine ⟨4360040471946872804327713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5813387295929163739103617 4360040471946872804327713)
          ·
            refine ⟨3270030353960154603245785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360040471946872804327713 3270030353960154603245785)
            ·
              refine ⟨2452522765470115952434339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3270030353960154603245785 2452522765470115952434339)
              ·
                refine ⟨3678784148205173928651509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452522765470115952434339 3678784148205173928651509)
                ·
                  refine ⟨344886013894235055811079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3678784148205173928651509 344886013894235055811079)
                  ·
                    rfl

theorem cell22_3022484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_3022484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022484 prefixEnd_3022484 := by exact prefixLift 3022484
  have htrace : WordTrace (prefixWord ++ tailWord_3022484) baseStart_3022484 baseEnd_3022484 := by
    simpa [prefixWord, tailWord_3022484, baseEnd_3022484] using wordTrace_append hprefix tailTrace_3022484
  have hstable : (prefixWord ++ tailWord_3022484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022484).length < 2 ^ (prefixWord ++ tailWord_3022484).sum := by decide
  have hdescent : baseEnd_3022484 < baseStart_3022484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022493 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3022493 : Nat := 118140960795 + 3022493 * 2 ^ 59
def prefixEnd_3022493 : Nat := 4983230072969 + 3 ^ 40 * 3022493 * 2
def baseEnd_3022493 : Nat := 1034661122566632143958209

theorem tailTrace_3022493 : CollatzResearch.WordTrace tailWord_3022493 prefixEnd_3022493 1034661122566632143958209 := by
  unfold tailWord_3022493
  simp only [CollatzResearch.WordTrace]
  refine ⟨110239376239031536552672133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73492917492687691035114755 110239376239031536552672133)
  ·
    refine ⟨20669883044818413103626025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110239376239031536552672133 20669883044818413103626025)
    ·
      refine ⟨15502412283613809827719519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20669883044818413103626025 15502412283613809827719519)
      ·
        refine ⟨23253618425420714741579279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15502412283613809827719519 23253618425420714741579279)
        ·
          refine ⟨34880427638131072112368919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23253618425420714741579279 34880427638131072112368919)
          ·
            refine ⟨52320641457196608168553379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34880427638131072112368919 52320641457196608168553379)
            ·
              refine ⟨78480962185794912252830069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52320641457196608168553379 78480962185794912252830069)
              ·
                refine ⟨7357590204918273023702819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78480962185794912252830069 7357590204918273023702819)
                ·
                  refine ⟨11036385307377409535554229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7357590204918273023702819 11036385307377409535554229)
                  ·
                    refine ⟨1034661122566632143958209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11036385307377409535554229 1034661122566632143958209)
                    ·
                      rfl

theorem cell22_3022493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3022493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022493 prefixEnd_3022493 := by exact prefixLift 3022493
  have htrace : WordTrace (prefixWord ++ tailWord_3022493) baseStart_3022493 baseEnd_3022493 := by
    simpa [prefixWord, tailWord_3022493, baseEnd_3022493] using wordTrace_append hprefix tailTrace_3022493
  have hstable : (prefixWord ++ tailWord_3022493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022493).length < 2 ^ (prefixWord ++ tailWord_3022493).sum := by decide
  have hdescent : baseEnd_3022493 < baseStart_3022493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022497 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 1, 4]
def baseStart_3022497 : Nat := 118140960795 + 3022497 * 2 ^ 59
def prefixEnd_3022497 : Nat := 4983230072969 + 3 ^ 40 * 3022497 * 2
def baseEnd_3022497 : Nat := 1034662491848377466858197

theorem tailTrace_3022497 : CollatzResearch.WordTrace tailWord_3022497 prefixEnd_3022497 1034662491848377466858197 := by
  unfold tailWord_3022497
  simp only [CollatzResearch.WordTrace]
  refine ⟨110239522131017045235817745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73493014754011363490545163 110239522131017045235817745)
  ·
    refine ⟨82679641598262783926863309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110239522131017045235817745 82679641598262783926863309)
    ·
      refine ⟨31004865599348543972573741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82679641598262783926863309 31004865599348543972573741)
      ·
        refine ⟨11626824599755703989715153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31004865599348543972573741 11626824599755703989715153)
        ·
          refine ⟨8720118449816777992286365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11626824599755703989715153 8720118449816777992286365)
          ·
            refine ⟨3270044418681291747107387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8720118449816777992286365 3270044418681291747107387)
            ·
              refine ⟨4905066628021937620661081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270044418681291747107387 4905066628021937620661081)
              ·
                refine ⟨3678799971016453215495811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4905066628021937620661081 3678799971016453215495811)
                ·
                  refine ⟨5518199956524679823243717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678799971016453215495811 5518199956524679823243717)
                  ·
                    refine ⟨1034662491848377466858197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5518199956524679823243717 1034662491848377466858197)
                    ·
                      rfl

theorem cell22_3022497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_3022497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022497 prefixEnd_3022497 := by exact prefixLift 3022497
  have htrace : WordTrace (prefixWord ++ tailWord_3022497) baseStart_3022497 baseEnd_3022497 := by
    simpa [prefixWord, tailWord_3022497, baseEnd_3022497] using wordTrace_append hprefix tailTrace_3022497
  have hstable : (prefixWord ++ tailWord_3022497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022497).length < 2 ^ (prefixWord ++ tailWord_3022497).sum := by decide
  have hdescent : baseEnd_3022497 < baseStart_3022497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022572 : List Nat := [2, 2, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_3022572 : Nat := 118140960795 + 3022572 * 2 ^ 59
def prefixEnd_3022572 : Nat := 4983230072969 + 3 ^ 40 * 3022572 * 2
def baseEnd_3022572 : Nat := 1034688165881102271232967

theorem tailTrace_3022572 : CollatzResearch.WordTrace tailWord_3022572 prefixEnd_3022572 1034688165881102271232967 := by
  unfold tailWord_3022572
  simp only [CollatzResearch.WordTrace]
  refine ⟨55121128802872666522398985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73494838403830222029865313 55121128802872666522398985)
  ·
    refine ⟨41340846602154499891799239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55121128802872666522398985 41340846602154499891799239)
    ·
      refine ⟨62011269903231749837698859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41340846602154499891799239 62011269903231749837698859)
      ·
        refine ⟨93016904854847624756548289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62011269903231749837698859 93016904854847624756548289)
        ·
          refine ⟨69762678641135718567411217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93016904854847624756548289 69762678641135718567411217)
          ·
            refine ⟨52322008980851788925558413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69762678641135718567411217 52322008980851788925558413)
            ·
              refine ⟨19620753367819420847084405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52322008980851788925558413 19620753367819420847084405)
              ·
                refine ⟨1839445628233070704414163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19620753367819420847084405 1839445628233070704414163)
                ·
                  refine ⟨2759168442349606056621245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839445628233070704414163 2759168442349606056621245)
                  ·
                    refine ⟨1034688165881102271232967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2759168442349606056621245 1034688165881102271232967)
                    ·
                      rfl

theorem cell22_3022572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_3022572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022572 prefixEnd_3022572 := by exact prefixLift 3022572
  have htrace : WordTrace (prefixWord ++ tailWord_3022572) baseStart_3022572 baseEnd_3022572 := by
    simpa [prefixWord, tailWord_3022572, baseEnd_3022572] using wordTrace_append hprefix tailTrace_3022572
  have hstable : (prefixWord ++ tailWord_3022572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022572).length < 2 ^ (prefixWord ++ tailWord_3022572).sum := by decide
  have hdescent : baseEnd_3022572 < baseStart_3022572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022583 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 2, 5]
def baseStart_3022583 : Nat := 118140960795 + 3022583 * 2 ^ 59
def prefixEnd_3022583 : Nat := 4983230072969 + 3 ^ 40 * 3022583 * 2
def baseEnd_3022583 : Nat := 1034691931405901909207933

theorem tailTrace_3022583 : CollatzResearch.WordTrace tailWord_3022583 prefixEnd_3022583 1034691931405901909207933 := by
  unfold tailWord_3022583
  simp only [CollatzResearch.WordTrace]
  refine ⟨110242658808705481923448403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73495105872470321282298935 110242658808705481923448403)
  ·
    refine ⟨165363988213058222885172605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110242658808705481923448403 165363988213058222885172605)
    ·
      refine ⟨62011495579896833581939727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165363988213058222885172605 62011495579896833581939727)
      ·
        refine ⟨93017243369845250372909591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62011495579896833581939727 93017243369845250372909591)
        ·
          refine ⟨139525865054767875559364387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93017243369845250372909591 139525865054767875559364387)
          ·
            refine ⟨209288797582151813339046581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139525865054767875559364387 209288797582151813339046581)
            ·
              refine ⟨19620824773326732500535617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209288797582151813339046581 19620824773326732500535617)
              ·
                refine ⟨14715618579995049375401713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19620824773326732500535617 14715618579995049375401713)
                ·
                  refine ⟨11036713934996287031551285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14715618579995049375401713 11036713934996287031551285)
                  ·
                    refine ⟨1034691931405901909207933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11036713934996287031551285 1034691931405901909207933)
                    ·
                      rfl

theorem cell22_3022583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_3022583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022583 prefixEnd_3022583 := by exact prefixLift 3022583
  have htrace : WordTrace (prefixWord ++ tailWord_3022583) baseStart_3022583 baseEnd_3022583 := by
    simpa [prefixWord, tailWord_3022583, baseEnd_3022583] using wordTrace_append hprefix tailTrace_3022583
  have hstable : (prefixWord ++ tailWord_3022583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022583).length < 2 ^ (prefixWord ++ tailWord_3022583).sum := by decide
  have hdescent : baseEnd_3022583 < baseStart_3022583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022602 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_3022602 : Nat := 118140960795 + 3022602 * 2 ^ 59
def prefixEnd_3022602 : Nat := 4983230072969 + 3 ^ 40 * 3022602 * 2
def baseEnd_3022602 : Nat := 344899478498064064327625

theorem tailTrace_3022602 : CollatzResearch.WordTrace tailWord_3022602 prefixEnd_3022602 344899478498064064327625 := by
  unfold tailWord_3022602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27560837948909162042097515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73495567863757765445593373 27560837948909162042097515)
  ·
    refine ⟨41341256923363743063146273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27560837948909162042097515 41341256923363743063146273)
    ·
      refine ⟨31005942692522807297359705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41341256923363743063146273 31005942692522807297359705)
      ·
        refine ⟨23254457019392105473019779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31005942692522807297359705 23254457019392105473019779)
        ·
          refine ⟨34881685529088158209529669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23254457019392105473019779 34881685529088158209529669)
          ·
            refine ⟨6540316036704029664286813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34881685529088158209529669 6540316036704029664286813)
            ·
              refine ⟨2452618513764011124107555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6540316036704029664286813 2452618513764011124107555)
              ·
                refine ⟨3678927770646016686161333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452618513764011124107555 3678927770646016686161333)
                ·
                  refine ⟨344899478498064064327625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3678927770646016686161333 344899478498064064327625)
                  ·
                    rfl

theorem cell22_3022602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_3022602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022602 prefixEnd_3022602 := by exact prefixLift 3022602
  have htrace : WordTrace (prefixWord ++ tailWord_3022602) baseStart_3022602 baseEnd_3022602 := by
    simpa [prefixWord, tailWord_3022602, baseEnd_3022602] using wordTrace_append hprefix tailTrace_3022602
  have hstable : (prefixWord ++ tailWord_3022602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022602).length < 2 ^ (prefixWord ++ tailWord_3022602).sum := by decide
  have hdescent : baseEnd_3022602 < baseStart_3022602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022632 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3022632 : Nat := 118140960795 + 3022632 * 2 ^ 59
def prefixEnd_3022632 : Nat := 4983230072969 + 3 ^ 40 * 3022632 * 2
def baseEnd_3022632 : Nat := 1034708705107282114732783

theorem tailTrace_3022632 : CollatzResearch.WordTrace tailWord_3022632 prefixEnd_3022632 1034708705107282114732783 := by
  unfold tailWord_3022632
  simp only [CollatzResearch.WordTrace]
  refine ⟨55122222992763981645991075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73496297323685308861321433 55122222992763981645991075)
  ·
    refine ⟨82683334489145972468986613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55122222992763981645991075 82683334489145972468986613)
    ·
      refine ⟨7751562608357434918967495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82683334489145972468986613 7751562608357434918967495)
      ·
        refine ⟨11627343912536152378451243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7751562608357434918967495 11627343912536152378451243)
        ·
          refine ⟨17441015868804228567676865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11627343912536152378451243 17441015868804228567676865)
          ·
            refine ⟨13080761901603171425757649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17441015868804228567676865 13080761901603171425757649)
            ·
              refine ⟨9810571426202378569318237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13080761901603171425757649 9810571426202378569318237)
              ·
                refine ⟨3678964284825891963494339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9810571426202378569318237 3678964284825891963494339)
                ·
                  refine ⟨5518446427238837945241509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678964284825891963494339 5518446427238837945241509)
                  ·
                    refine ⟨1034708705107282114732783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5518446427238837945241509 1034708705107282114732783)
                    ·
                      rfl

theorem cell22_3022632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3022632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022632 prefixEnd_3022632 := by exact prefixLift 3022632
  have htrace : WordTrace (prefixWord ++ tailWord_3022632) baseStart_3022632 baseEnd_3022632 := by
    simpa [prefixWord, tailWord_3022632, baseEnd_3022632] using wordTrace_append hprefix tailTrace_3022632
  have hstable : (prefixWord ++ tailWord_3022632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022632).length < 2 ^ (prefixWord ++ tailWord_3022632).sum := by decide
  have hdescent : baseEnd_3022632 < baseStart_3022632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022677 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_3022677 : Nat := 118140960795 + 3022677 * 2 ^ 59
def prefixEnd_3022677 : Nat := 4983230072969 + 3 ^ 40 * 3022677 * 2
def baseEnd_3022677 : Nat := 1034724109526916997357645

theorem tailTrace_3022677 : CollatzResearch.WordTrace tailWord_3022677 prefixEnd_3022677 1034724109526916997357645 := by
  unfold tailWord_3022677
  simp only [CollatzResearch.WordTrace]
  refine ⟨110246087270364935977370285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73497391513576623984913523 110246087270364935977370285)
  ·
    refine ⟨41342282726386850991513857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110246087270364935977370285 41342282726386850991513857)
    ·
      refine ⟨31006712044790138243635393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41342282726386850991513857 31006712044790138243635393)
      ·
        refine ⟨23255034033592603682726545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31006712044790138243635393 23255034033592603682726545)
        ·
          refine ⟨17441275525194452762044909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23255034033592603682726545 17441275525194452762044909)
          ·
            refine ⟨6540478321947919785766841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17441275525194452762044909 6540478321947919785766841)
            ·
              refine ⟨4905358741460939839325131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6540478321947919785766841 4905358741460939839325131)
              ·
                refine ⟨7358038112191409758987697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4905358741460939839325131 7358038112191409758987697)
                ·
                  refine ⟨5518528584143557319240773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7358038112191409758987697 5518528584143557319240773)
                  ·
                    refine ⟨1034724109526916997357645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5518528584143557319240773 1034724109526916997357645)
                    ·
                      rfl

theorem cell22_3022677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_3022677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022677 prefixEnd_3022677 := by exact prefixLift 3022677
  have htrace : WordTrace (prefixWord ++ tailWord_3022677) baseStart_3022677 baseEnd_3022677 := by
    simpa [prefixWord, tailWord_3022677, baseEnd_3022677] using wordTrace_append hprefix tailTrace_3022677
  have hstable : (prefixWord ++ tailWord_3022677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022677).length < 2 ^ (prefixWord ++ tailWord_3022677).sum := by decide
  have hdescent : baseEnd_3022677 < baseStart_3022677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022698 : List Nat := [3, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_3022698 : Nat := 118140960795 + 3022698 * 2 ^ 59
def prefixEnd_3022698 : Nat := 4983230072969 + 3 ^ 40 * 3022698 * 2
def baseEnd_3022698 : Nat := 344910432752026647527527

theorem tailTrace_3022698 : CollatzResearch.WordTrace tailWord_3022698 prefixEnd_3022698 344910432752026647527527 := by
  unfold tailWord_3022698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27561713300822214140971187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73497902135525904375923165 27561713300822214140971187)
  ·
    refine ⟨41342569951233321211456781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27561713300822214140971187 41342569951233321211456781)
    ·
      refine ⟨15503463731712495454296293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41342569951233321211456781 15503463731712495454296293)
      ·
        refine ⟨2906899449696092897680555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15503463731712495454296293 2906899449696092897680555)
        ·
          refine ⟨4360349174544139346520833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2906899449696092897680555 4360349174544139346520833)
          ·
            refine ⟨3270261880908104509890625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360349174544139346520833 3270261880908104509890625)
            ·
              refine ⟨2452696410681078382417969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3270261880908104509890625 2452696410681078382417969)
              ·
                refine ⟨1839522308010808786813477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452696410681078382417969 1839522308010808786813477)
                ·
                  refine ⟨344910432752026647527527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1839522308010808786813477 344910432752026647527527)
                  ·
                    rfl

theorem cell22_3022698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_3022698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022698 prefixEnd_3022698 := by exact prefixLift 3022698
  have htrace : WordTrace (prefixWord ++ tailWord_3022698) baseStart_3022698 baseEnd_3022698 := by
    simpa [prefixWord, tailWord_3022698, baseEnd_3022698] using wordTrace_append hprefix tailTrace_3022698
  have hstable : (prefixWord ++ tailWord_3022698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022698).length < 2 ^ (prefixWord ++ tailWord_3022698).sum := by decide
  have hdescent : baseEnd_3022698 < baseStart_3022698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022720 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 5]
def baseStart_3022720 : Nat := 118140960795 + 3022720 * 2 ^ 59
def prefixEnd_3022720 : Nat := 4983230072969 + 3 ^ 40 * 3022720 * 2
def baseEnd_3022720 : Nat := 344912943101893072844171

theorem tailTrace_3022720 : CollatzResearch.WordTrace tailWord_3022720 prefixEnd_3022720 344912943101893072844171 := by
  unfold tailWord_3022720
  simp only [CollatzResearch.WordTrace]
  refine ⟨55123827804604577160592807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73498437072806102880790409 55123827804604577160592807)
  ·
    refine ⟨82685741706906865740889211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55123827804604577160592807 82685741706906865740889211)
    ·
      refine ⟨124028612560360298611333817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82685741706906865740889211 124028612560360298611333817)
      ·
        refine ⟨93021459420270223958500363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124028612560360298611333817 93021459420270223958500363)
        ·
          refine ⟨139532189130405335937750545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93021459420270223958500363 139532189130405335937750545)
          ·
            refine ⟨104649141847804001953312909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139532189130405335937750545 104649141847804001953312909)
            ·
              refine ⟨39243428192926500732492341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104649141847804001953312909 39243428192926500732492341)
              ·
                refine ⟨3679071393086859443671157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39243428192926500732492341 3679071393086859443671157)
                ·
                  refine ⟨344912943101893072844171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3679071393086859443671157 344912943101893072844171)
                  ·
                    rfl

theorem cell22_3022720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_3022720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3022720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3022720 prefixEnd_3022720 := by exact prefixLift 3022720
  have htrace : WordTrace (prefixWord ++ tailWord_3022720) baseStart_3022720 baseEnd_3022720 := by
    simpa [prefixWord, tailWord_3022720, baseEnd_3022720] using wordTrace_append hprefix tailTrace_3022720
  have hstable : (prefixWord ++ tailWord_3022720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022720).length < 2 ^ (prefixWord ++ tailWord_3022720).sum := by decide
  have hdescent : baseEnd_3022720 < baseStart_3022720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
